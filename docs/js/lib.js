/* Copyright (C) 1991-2017 Free Software Foundation, Inc.
   This file is part of the GNU C Library.

   The GNU C Library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2.1 of the License, or (at your option) any later version.

   The GNU C Library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public
   License along with the GNU C Library; if not, see
   <http://www.gnu.org/licenses/>.  */
/* This header is separate from features.h so that the compiler can
   include it implicitly at the start of every compilation.  It must
   not itself include <features.h> or any other header that includes
   <features.h> because the implicit include comes before any feature
   test macros that may be defined in a source file before it first
   explicitly includes a system header.  GCC knows the name of this
   header in order to preinclude it.  */
/* glibc's intent is to support the IEC 559 math functionality, real
   and complex.  If the GCC (4.9 and later) predefined macros
   specifying compiler intent are available, use them to determine
   whether the overall intent is to support these features; otherwise,
   presume an older compiler has intent to support these features and
   define these macros by default.  */
/* wchar_t uses Unicode 8.0.0.  Version 8.0 of the Unicode Standard is
   synchronized with ISO/IEC 10646:2014, plus Amendment 1 (published
   2015-05-15).  */
/* We do not support C11 <threads.h>.  */
/*
   GHCJS bignum library for integer-gmp package

   uses JavaScript arrays for big numbers
   some algorithms and code based on JSBN by Tom Wu

   Copyright Luite Stegeman 2016
 */
// values defined in Gen2.ClosureInfo
// thread status
/*
 * low-level heap object manipulation macros
 */
// GHCJS.Prim.JSVal
// GHCJS.Prim.JSException
// Exception dictionary for JSException
// SomeException
// GHC.Ptr.Ptr
// GHC.Integer.GMP.Internals
// Data.Maybe.Maybe
// #define HS_NOTHING h$nothing
// Data.List
// Data.Text
// Data.Text.Lazy
// black holes
// can we skip the indirection for black holes?
// resumable thunks
// general deconstruction
// retrieve  a numeric value that's possibly stored as an indirection
// generic lazy values
// generic data constructors and selectors
// unboxed tuple returns
// #define RETURN_UBX_TUP1(x) return x;
// #define GHCJSBN_TRACE_INTEGER 1
// bits per limb
// BI_FP = 52
// BI_FP - GHCJSBN_BITS
// 2*GHCJSBN_BITS - BI_FP
// 2 ^ BI_FP
// values for the Haskell Ordering enum
var h$ghcjsbn_zero_i = (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziSzh_con_e, (0)));;
var h$ghcjsbn_one_i = (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziSzh_con_e, (1)));;
var h$ghcjsbn_negOne_i = (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziSzh_con_e, (-1)));;
var h$ghcjsbn_null_b = [-1];
var h$ghcjsbn_zero_b = [0];
var h$ghcjsbn_one_b = [1, 1];
var h$ghcjsbn_two31_b = [2, 0, 8];
var h$ghcjsbn_czero_b = [2, 268435455, 15];
var h$ghcjsbn_two31_i = (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziJpzh_con_e, (h$ghcjsbn_two31_b)));;
var h$ghcjsbn_negTwo31_i = (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziSzh_con_e, (-2147483648)));;
/******************************************************************************

 Types used here:
   - b BigNat:  array of limbs (each a number of GHCJSBN_BITS bits)
   - s Int:     small integer in range -2^31 .. 2^31-1
   - w Word:    small integer in range 0 .. 2^32-1,
                  values greater than 2^31-1 are stored as negative numbers
   - i Integer: Haskell Integer heap object, see invariants

 Integer invariants:
   - BigNat arrays do not have leading zeroes
   - Jp > S > Jn
   - S range: -2^31 .. 2^31-1 (-2147483648 .. 2147483647)

 ******************************************************************************/
// checks that the S,Jn,Jp constructor invariants hold
function h$ghcjsbn_assertValid_i(b, msg) {
  var sd, d, neg, i, n;
  // check global constants for unwanted mutations
  if(h$ghcjsbn_zero_b.length !== 1 || h$ghcjsbn_zero_b[0] !== 0) {
    throw new Error("zero_b mutated");
  }
  if(h$ghcjsbn_one_b.length !== 2 || h$ghcjsbn_one_b[0] !== 1 || h$ghcjsbn_one_b[1] !== 1) {
    throw new Error("one_b mutated");
  }
  if(((b).f === h$integerzmgmpZCGHCziIntegerziTypeziSzh_con_e)) {
    sd = ((b).d1);
    if(typeof sd !== 'number')
      throw new Error("invalid small integer: not a number");
    if((sd|0) !== sd)
      throw new Error("invalid small integer: not a small int");
  } else {
    if(((b).f === h$integerzmgmpZCGHCziIntegerziTypeziJpzh_con_e)) {
      neg = false;
    } else if(((b).f === h$integerzmgmpZCGHCziIntegerziTypeziJnzh_con_e)) {
      neg = true;
    } else {
      throw new Error("invalid integer: unexpected constructor");
    }
    d = ((b).d1);
    h$ghcjsbn_assertValid_b(d, "assertValid_i");
    if(d[0] < 2)
      throw new Error("invalid big integer: array too short");
    if(d[0] === 2) {
      if((d[2] >> (31-28)) === 0 ||
         (neg && d[2] === 0x20 && d[1] === 0))
        throw new Error("invalid big integer: in smallint range");
    }
    // everything ok
  }
}
// checks invariant for big number
function h$ghcjsbn_assertValid_b(d, msg) {
  var i, n;
  if(!Array.isArray(d))
    throw new Error("invalid big integer: not an array");
  if(typeof d[0] !== 'number' || d[0] > (d.length-1))
    throw new Error("invalid big integer: incorrect number of limbs");
  if(d[0] > 0 && d[d[0]] === 0)
    throw new Error("invalid big integer: leading zero");
  for(i = 1; i <= d[0]; i++) {
    n = d[i];
    if(typeof n !== 'number')
      throw new Error("invalid big integer: limb is not a number");
    if((n & 0xfffffff) !== n)
      throw new Error("invalid big integer: limb out of range");
  }
}
function h$ghcjsbn_assertValid_s(s, msg) {
  if(typeof s !== 'number')
    throw new Error("invalid int: not a number");
  if((s|0) !== s)
    throw new Error("invalid int: not in smallint range");
}
function h$ghcjsbn_assertValid_w(w, msg) {
  if(typeof w !== 'number')
    throw new Error("invalid word: not a number");
  if((w|0) !== w)
    throw new Error("invalid word: not in smallint range");
}
function h$ghcjsbn_assertValid_d(d, msg) {
  if(typeof d !== 'number')
    throw new Error("invalid double: not a number");
}
/******************************************************************************/
///////////////////////////////////////////////////////////////////////////////
// the ghcjsbn_r functions operate on the raw array data directly
///////////////////////////////////////////////////////////////////////////////
var h$ghcjsbn_smallPrimes =
 [ 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47
 , 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113
 , 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197
 , 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281
 , 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379
 , 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463
 , 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571
 , 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659
 , 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761
 , 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863
 , 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977
 , 983, 991, 997
 ];
var h$ghcjsbn_smallPrimesM = null;
function h$ghcjsbn_getSmallPrimesM() {
  var a, i;
  if(h$ghcjsbn_smallPrimesM === null) {
    a = [];
    for(i = 0; i < 1008; i++) {
      a[i] = false;
    }
    for(i = h$ghcjsbn_smallPrimes.length - 1; i >= 0; i--) {
      a[h$ghcjsbn_smallPrimes[i]] = true;
    }
    h$ghcjsbn_smallPrimesM = a;
  }
  return h$ghcjsbn_smallPrimesM;
}
// Int -> Int -> Bool
// fixme: seed
function h$ghcjsbn_isPrime_s(s, rounds) {
  if(s < 2 || (s > 2 && ((s&1) === 1))) return false;
  if(s <= 1008) {
    return h$ghcjsbn_getSmallPrimesM()[s];
  }
  throw new Error("isPrime_s");
}
// BigNat -> Int -> Bool
// fixme: seed
function h$ghcjsbn_isPrime_b(b, rounds) {
  h$ghcjsbn_assertValid_b(b, "isPrime");
  throw new Error("isPrime_b");
}
// BigNat -> BigNat -> Bool
/*
function h$ghcjsbn_eq_bb(b1, b2) {
  ASSERTVALID_B(b1, "eq_bb b1");
  ASSERTVALID_B(b2, "eq_bb b2");
  var l1 = b1.length, l2 = b2.length;
  if(l1 !== l2) return false;
  while(--l1 >= 0) {
    if(b1[l1] !== b2[l1]) return false;
  }
  return true;
}
*/
// BigNat -> BigNat -> Int (Ordering: LT,EQ,GT)
function h$ghcjsbn_cmp_bb(b1, b2) {
  h$ghcjsbn_assertValid_b(b1, "cmp_bb b1");
  h$ghcjsbn_assertValid_b(b2, "cmp_bb b2");
  var l1 = b1[0], l2 = b2[0], d1, d2;
  if(l1 === l2) {
    while(--l1 >= 0) {
      d1 = b1[l1+1];
      d2 = b2[l1+1];
      if(d1 !== d2) return d1 < d2 ? 0 : 2;
    }
    return 1;
  } else {
    return l1 > l2 ? 2 : 0;
  }
}
// fixed size tmp, these should not grow
var h$ghcjsbn_tmp_2a = [0, 0, 0];
var h$ghcjsbn_tmp_2b = [0, 0, 0];
// this is variable size scratch space
var h$ghcjsbn_tmp_a = [0, 0, 0, 0, 0, 0, 0, 0];
var h$ghcjsbn_tmp_b = [0, 0, 0, 0, 0, 0, 0, 0];
// b - w :: BigNat -> Word -> BigNat
function h$ghcjsbn_sub_bw(b, w) {
  var a = h$ghcjsbn_tmp_2a;
  h$ghcjsbn_toBigNat_w(a, w);
  return h$ghcjsbn_sub_bb(b, a);
}
// b - s :: BigNat -> Int -> BigNat
// returns new BigNat, nullBigNat in case of underflow
// returns size of t
function h$ghcjsbn_sub_bs(b, s) {
  h$ghcjsbn_assertValid_b(b, "sub_bs");
  h$ghcjsbn_assertValid_s(s, "sub_bs");
  var a, ms, r;
  if(s < 0) {
    if(s === -2147483648) {
      r = h$ghcjsbn_add_bb(b, h$ghcjsbn_two31_b);
    } else {
      a = h$ghcjsn_tmp_2a;
      h$ghcjsbn_toBigNat_s(a, -s);
      r = h$ghcjsbn_add_bb(b, a);
    }
  } else {
    a = h$ghcjsn_tmp_2a;
    h$ghcjsbn_toBigNat_s(a, s);
    r = h$ghcjsbn_sub_bb(b, a);
  }
  h$ghcjsbn_assertValid_b(r, "sub_bs result");
  return r;
}
// t = b + w :: BigNat -> BigNat -> Word -> Int
// returns size of t
function h$ghcjsbn_add_bw(b, w) {
  h$ghcjsbn_assertValid_b(b, "add_bw");
  h$ghcjsbn_assertValid_w(w, "add_bw");
  var a = h$ghcjsbn_tmp_2a;
  h$ghcjsbn_toBigNat_w(a, w);
  return h$ghcjsbn_add_bb(b, a);
}
// t = b + s :: BigNat -> BigNat -> Int -> Int
// returns size of t, nullBigNat in case of underflow
function h$ghcjsbn_add_bs(b, s) {
  h$ghcjsbn_assertValid_b(b, "add_bs");
  h$ghcjsbn_assertValid_s(s, "add_bs");
  var a, ms, r;
  if(s < 0) {
    if(s === -2147483648) {
      r = h$ghcjsbn_sub_bb(b, h$ghcjsbn_two31_r);
    } else {
      ms = -s;
      a = h$ghcjsbn_tmp_2a;
      h$ghcjsbn_toBigNat_s(a, ms);
      r = h$ghcjsbn_sub(b, a);
    }
  } else {
    a = h$ghcjsbn_tmp_2a;
    h$ghcjsbn_toBigNat_s(a, s);
    r = h$ghcjsbn_add_bb(b, a);
  }
  h$ghcjsbn_assertValid_b(r, "add_bs result");
  return r;
}
// t = b1 + b2 :: BigNat -> BigNat -> BigNat -> Int
// returns size of t
function h$ghcjsbn_add_bb(b1, b2) {
  h$ghcjsbn_assertValid_b(b1, "add_bb b1");
  h$ghcjsbn_assertValid_b(b2, "add_bb b2");
  var i, c = 0, l1 = b1[0], l2 = b2[0], t = [0];
  var bl, lmin, lmax;
  if(l1 <= l2) {
    lmin = l1;
    lmax = l2;
    bl = b2;
  } else {
    lmin = l2;
    lmax = l1;
    bl = b1;
  }
  for(i=1;i<=lmin;i++) {
    c += b1[i] + b2[i];
    t[i] = c & 0xfffffff;
    c >>= 28;
  }
  for(i=lmin+1;i<=lmax;i++) {
    c += bl[i];
    t[i] = c & 0xfffffff;
    c >>= 28;
  }
  if(c !== 0) t[++lmax] = c;
  t[0] = lmax;
  h$ghcjsbn_assertValid_b(t, "add_bb result");
  return t;
}
// b1 += b2 :: BigNat -> BigNat -> Int
// returns new size of b1
function h$ghcjsbn_addTo_bb(b1, b2) {
  h$ghcjsbn_assertValid_b(b1, "addTo_bb b1");
  h$ghcjsbn_assertValid_b(b2, "addTo_bb b2");
  var i, c = 0, l1 = b1[0], l2 = b2[0];
  if(l2 > l1) {
    for(i = l1 + 1; i <= l2; i++) {
      b1[i] = 0;
    }
    l1 = l2;
  }
  for(i = 1; i <= l2; i++) {
    c += b1[i] + b2[i];
    b1[i] = c & 0xfffffff;
    c >>= 28;
  }
  // propagate carry as long as needed
  for(i = l2 + 1; c !== 0 && i <= l1; i++) {
    c += b1[i];
    b1[i] = c & 0xfffffff;
    c >>= 28;
  }
  if(c !== 0) {
    b1[l1] = c;
    b1[0] = l1+1;
  } else {
    b1[0] = l1;
  }
  h$ghcjsbn_assertValid_b(b1, "addTo_bb result");
}
// b1 - b2 :: BigNat -> BigNat -> BigNat
// returns a new BigNat, nullBigNat in case of underflow
function h$ghcjsbn_sub_bb(b1, b2) {
  h$ghcjsbn_assertValid_b(b1, "sub_bb b1");
  h$ghcjsbn_assertValid_b(b2, "sub_bb b2");
  if(h$ghcjsbn_cmp_bb(b1,b2) === 0) {
    return [];
  } else {
    var i, c = 0, l1 = b1[0], l2 = b2[0], t = [0];
    for(i = 1; i <= l2; i++) {
      c += b1[i] - b2[i];
      t[i] = c & 0xfffffff;
      c >>= 28;
    }
    for(i = l2 + 1; i <= l1; i++) {
      c += b1[i];
      t[i] = c & 0xfffffff;
      c >>= 28;
    }
    while(l1 > 0 && t[l1] === 0) l1--;
    t[0] = l1;
    h$ghcjsbn_assertValid_b(t, "sub_bb result");
    return t;
  }
}
// b1 -= b2 :: BigNat -> BigNat -> Int
// returns size of t, b1 must be >= b2
function h$ghcjsbn_subTo_bb(b1, b2) {
  h$ghcjsbn_assertValid_b(b1, "subTo_bb b1");
  h$ghcjsbn_assertValid_b(b2, "subTo_bb b2");
  if(h$ghcjsbn_cmp_bb(b1, b2) === 0) {
    throw new Error("h$ghcjsbn_subTo_bb assertion failed: b1 >= b2");
  }
  var i, c = 0, l1 = b1[0], l2 = b2[0];
  for(i = 1; i <= l2; i++) {
    c += b1[i] - b2[i];
    b1[i] = c & 0xfffffff;
    c >>= 28;
  }
  for(i = l2 + 1; c !== 0 && i <= l1; i++) {
    c += b1[i];
    b1[i] = c & 0xfffffff;
    c >>= 28;
  }
  while(l1 > 0 && b1[l1] === 0) l1--;
  b1[0] = l1;
  h$ghcjsbn_assertValid_b(b1, "subTo_bb result");
}
// t = b1 / b2, BigNat -> BigNat -> BigNat -> Int (returns size of t)
/* function h$ghcjsbn_div_bb(t, b1, b2) {

}

// t = b1 % b2, BigNat -> BigNat -> BigNat -> Int (returns size of t)
function h$ghcjsbn_mod_bb(t, b1, b2) {

}

// b % s, BigNat -> Int -> Int
function h$ghcjsbn_mod_bs(b, s) {

}
*/
// BigNat -> Integer (nonnegative, known length)
/*
function h$ghcjsbn_wrap_pl(b, l) {
  var lb;
  if(l === 0) {
    return MK_INTEGER_S(0);
  } else if(l === 1) {
    return MK_INTEGER_S(b[0]);
  } else if(l === 2 && (b[1] >> (31 - GHCJSBN_BITS)) === 0) {
    return MK_INTEGER_S((b[1] << GHCJSBN_BITS)|b[0]);
  } else {
    lb = b.length - l;
    while(lb-- > 0) b.pop();
    return MK_INTEGER_Jp(b);
  }
}
*/
// BigNat -> Integer (nonnegative)
function h$ghcjsbn_wrap_p(b) {
  var l = b[0];
  if(l === 0) {
    return (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziSzh_con_e, (0)));;
  } else if(l === 1) {
    return (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziSzh_con_e, (b[1])));;
  } else if(l === 2 && (b[2] >> (31 - 28)) === 0) {
    return (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziSzh_con_e, ((b[2] << 28)|b[1])));;
  } else {
    return (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziJpzh_con_e, (b)));;
  }
}
/*
function h$ghcjsbn_wrap_nl(b, l) {
  var lb;
  if(l === 0) {
    return MK_INTEGER_S(0);
  } else if(l === 1) {
    return MK_INTEGER_S(-b[0]);
  } else if(l === 2 &&
            ((b[1] >> (31 - GHCJSN_BITS)) === 0 ||
             (b[1] === (1 << (31 - GHCJSBN_BITS)) && b[0] === 0))) {
    return MK_INTEGER_S((-b[1]-b[0])|0);
  } else {
    lb = b.length - l;
    while(lb-- > 0) b.pop();
    return MK_INTEGER_Jn(b);
  }
}
*/
// BigNat -> Integer (nonnegative)
function h$ghcjsbn_wrap_n(b) {
  var l = b[0];
  if(l === 0) {
    return (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziSzh_con_e, (0)));;
  } else if(l === 1) {
    return (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziSzh_con_e, (-b[1])));;
  } else if(l === 2 &&
            ((b[2] >> (31 - GHCJSN_BITS)) === 0 ||
             (b[2] === (1 << (31 - 28)) && b[1] === 0))) {
    return (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziSzh_con_e, ((-b[2]-b[1])|0)));;
  } else {
    return (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziJnzh_con_e, (b)));;
  }
}
// b1 *= b2 :: BigNat -> BigNat -> IO ()
function h$ghcjsbn_mulTo_bb(b1, b2) {
  h$ghcjsbn_assertValid_b(b1, "mulTo_bb b1");
  h$ghcjsbn_assertValid_b(b2, "mulTo_bb b2");
  var t = h$ghcjsbn_mul_bb(b1, b2);
  h$ghcjsbn_copy(b1, t);
  h$ghcjsbn_assertValid_b(b1, "mulTo_bb result");
}
// b1 * b2 ::  BigNat -> BigNat -> BigNat
function h$ghcjsbn_mul_bb(b1, b2) {
  h$ghcjsbn_assertValid_b(b1, "mul_bb b1");
  h$ghcjsbn_assertValid_b(b2, "mul_bb b2");
  var l1 = b1[0], l2 = b2[0];
/*  if(l1 > 50 && l2 > 50) {
    return h$ghcjsbn_mul_karatsuba_bb(b1, b2);
  } fixme update this */
  var n = l1 + l2, i, t = [0];
  for(i = 1; i <= n; i++) t[i] = 0;
  if(l1 > l2) {
    for(i = 0; i < l2; i++) {
      t[i + l1 + 1] = h$ghcjsbn_mul_limb(0, b1, b2[i+1], t, i, 0, l1);
    }
  } else {
    for(i = 0; i < l1; i++) {
      t[i + l2 + 1] = h$ghcjsbn_mul_limb(0, b2, b1[i+1], t, i, 0, l2);
    }
  }
  for(i = l1 + l2; i > 0 && t[i] === 0; i--);
  t[0] = i;
  h$ghcjsbn_assertValid_b(t, "mul_bb result");
  return t;
}
function h$ghcjsbn_mul_bw(b, w) {
  h$ghcjsbn_assertValid_b(b, "mul_bw");
  h$ghcjsbn_assertValid_w(w, "mul_bw");
  var a = h$ghcjsbn_tmp_2a;
  h$ghcjsbn_toBigNat_w(a, w);
  var t = h$ghcjsbn_mul_bb(b, a);
  h$ghcjsbn_assertValid_b(t, "mul_bw result");
  return t;
}
// karatzuba multiplication for long numbers
function h$ghcjsbn_mul_karatsuba_bb(t, b1, b2) {
  throw new Error("not yet updated");
  var l1 = b1.length, l2 = b2.length;
  var i, b = (l1 < l2 ? l1 : l2) >> 1;
  var x0 = [b], x1 = [l1-b], y0 = [b], y1 = [l2-b];
  for(i = 1; i <= b; i++) {
    x0[i] = b1[i];
    y0[i] = b2[i];
  }
  for(i = b + 1; i <= l1; i++) x1[i - b] = b1[i];
  for(i = b + 1; i <= l2; i++) y1[i - b] = b2[i];
  var z0 = h$ghcjsbn_mul_bb(x0, y0), z1, z2 = h$ghcjsbn_mul_bb(x1, y1);
  // compute z1 = (x1 + x0)(y1 + y0) - z2 - z0
  // (reusing x0 and y0 for (x1 + x0) and (y1 + y0))
  h$ghcjsbn_addTo_bb(x0, x1);
  h$ghcjsbn_addTo_bb(y0, x1);
  z1 = h$ghcjsbn_mul_bb(x0, y0);
  h$ghcjsbn_subTo_bb(z1, z2);
  h$ghcjsbn_subTo_bb(z1, z0);
  // store shifted z2 in t
  // fixme this looks wrong
  for(i = 0; i < 2*b; i++) t[i] = 0;
  l2 = z2.length;
  for(i = 0; i < l2; i++) t[i+2*b] = z2[i];
  // compute shifted z1s = z1 * B
  var z1s = [];
  l1 = z1.length;
  for(i = 0; i < b; i++) z1s[i] = 0;
  for(i = 0; i < l1; i++) z1s[i+b] = z1[i];
  // add the results so that t = z2 * (2*B) + z1 * B + z0
  h$ghcjsbn_addTo_bb(t, z1s);
  h$ghcjsbn_addTo_bb(t, z0);
  return t;
}
// from JSBN am3
// w_j += (x*b_i) ?
/* c = carry?
   n = iterations?
 */
function h$ghcjsbn_mul_limb(i,b,x,w,j,c,n) {
  // ASSERTVALID_B(b, "mul_limb b");
  // ASSERTVALID_B(w, "mul_limb w");
  var xl = x & 0x3fff, xh = x >> 14;
  while(--n >= 0) {
    var l = b[++i] & 0x3fff;
    var h = b[i] >> 14;
    var m = xh * l + h * xl;
    l = xl *l + ((m & 0x3fff) << 14) + w[++j] + c;
    c = (l >> 28) + (m >> 14) + xh * h;
    // h$log("mul_limb: c: " + c + " l: " + l + " xh: " + xh + " h: " + h);
    w[j] = l & 0xfffffff;
  }
  return c;
}
// q = b1 / b2, r = b1 % b2 :: BigNat -> BigNat -> BigNat -> BigNat -> Int
// b2 must be > 0
// returns length of r
// d is normalized before return
/*
   algorithm:
 y = 0?
 nsh = number of leading zeroes in most significant word
 pm = positive modulus
 pt = positive divident
 y = tmp, shifted modulus
 r = shifted divident
 ys = length of y
 y0 = biggest limb of y
 yt = new estimated length of y?
 */
function h$ghcjsbn_quotRem_bb(q, r, b1, b2) {
  h$ghcjsbn_assertValid_b(b1, "quotRem_bb b1");
  h$ghcjsbn_assertValid_b(b2, "quotRem_bb b2");
  if(h$ghcjsbn_cmp_bw(b2, 0) !== 2) {
    throw new Error("h$ghcjsbn_quotRem_bb: operand not positive");
  }
  if(q === null) q = h$ghcjsbn_tmp_a;
  if(r === null) r = h$ghcjsbn_tmp_b;
  var l1 = b1[0], l2 = b2[0], nsh, y = [];
  if(l1 === 0) {
    q[0] = 0;
    r[0] = 0;
    return;
  }
  if(h$ghcjsbn_cmp_bb(b1,b2) === 0) {
    q[0] = 0;
    h$ghcjsbn_copy(r, b1);
    return;
  }
  nsh = 28 -h$ghcjsbn_nbits_s(b2[l2]);
  h$ghcjsbn_assertValid_s(nsh, "quotRem_bb nsh");
  if(nsh !== 0) {
    h$ghcjsbn_shlTo_b(y, b2, nsh);
    h$ghcjsbn_shlTo_b(r, b1, nsh);
  } else {
    h$ghcjsbn_copy(y, b2);
    h$ghcjsbn_copy(r, b1);
  }
  h$ghcjsbn_assertValid_b(y, "quotRem_bb y_0");
  h$ghcjsbn_assertValid_b(r, "quotRem_bb r_0");
  var ys = y[0], y0 = y[ys];
  var yt = y0*(1<<24)+((ys>1)?y[ys-1]>>4:0);
  var d1 = 4503599627370496/yt, d2 = (1<<24)/yt, e = 1 << 4;
  var i = r[0], j = i-ys, t = q;
  h$ghcjsbn_shlTo_limbs_b(t,y,j);
  // h$log("rt1: " + i);
  // h$log("[" + r.join(",") + "] [" + t.join(",") + "]");
  if(h$ghcjsbn_cmp_bb(r, t) !== 0) {
    r[r[0]+1] = 1;
    r[0] += 1;
    // h$log("rt1a: " + r[0]);
    h$ghcjsbn_subTo_bb(r, t);
  }
  // h$log("rt2: " + r[0]);
  // h$log("y0: " + y0 + " yt: " + yt + " d1: " + d1 + " d2: " + d2 + " e: " + e);
  h$ghcjsbn_shlTo_limbs_b(t, h$ghcjsbn_one_b, ys);
  y = h$ghcjsbn_sub_bb(t, y);
  while(y.length <= ys) y[y.length] = 0; // fixme? no looks ok
  while(--j >= 0) {
    // Estimate quotient digit
    var qd = (r[(--i)+1]===y0)?0xfffffff:Math.floor(r[i+1]*d1+(r[i]+e)*d2);
    // h$log("i: " + i + " j: " + j + " qd: " + qd + " rdi: " + r[i+1] + " ys: " + ys);
    // h$log("yd: [" + y.join(',') + "] rd: [" + r.join(',') + "]");
    var am = h$ghcjsbn_mul_limb(0, y, qd, r, j, 0, ys);
    // h$log("am: " + am);
    if((r[i+1] += am) < qd) {
    // if((r[i+1] += h$ghcjsbn_mul_limb(0, y, qd, r, j, 0, ys)) < qd) {
      h$ghcjsbn_shlTo_limbs_b(t, y, j);
      h$ghcjsbn_subTo_bb(r, t);
      // h$log("0. rdi: " + r[i+1] + " qd: " + qd);
      while(r[i+1] < --qd) {
        // h$log("1. rdi: " + r[i+1] + " qd: " + qd);
        h$ghcjsbn_subTo_bb(r, t);
      }
    }
  }
  h$ghcjsbn_assertValid_b(r, "intermediate r");
  h$ghcjsbn_shrTo_limbs_b(q, r, ys);
  r[0] = ys;
  while(r[r[0]] === 0 && r[0] > 0 && r[0]--);
  if(nsh !== 0) {
    var r0 = [];
    h$ghcjsbn_copy(r0, r);
    h$ghcjsbn_shrTo_b(r, r0, nsh);
  }
  h$ghcjsbn_assertValid_b(q, "quotRem_bb result q");
  h$ghcjsbn_assertValid_b(r, "quotRem_bb result r");
}
// b % w , q = b / w :: BigNat -> BigNat -> Word -> Word
function h$ghcjsbn_quotRem_bw(q, b, w) {
  h$ghcjsbn_assertValid_b(b, "quotRem_bw");
  h$ghcjsbn_assertValid_w(w, "quotRem_bw");
  var a = h$ghcjsbn_tmp_2a;
  h$ghcjsbn_toBigNat_w(a, w);
/*  if(w === 0) {
    a[0] = 0;
  } else if(w > 0 && w <= GHCJSBN_MASK) {
    a[0] = 1;
    a[1] = w;
  } else {
    a[0] = 2;
    a[1] = w   & GHCJSBN_MASK;
    a[2] = w >>> GHCJSBN_BITS;
  } */
  var r = [];
  h$ghcjsbn_quotRem_bb(q, r, b, a);
  return h$ghcjsbn_toWord_b(r);
}
// BigNat -> JSBN
// assumes same number of bits
function h$ghcjsbn_tmp_toJSBN(b) {
  var j = new BigInteger(), bl = b[0], i;
  for(i = 0; i < bl; i++) j.data[i] = b[i+1];
  j.s = 0;
  j.t = bl;
  return j;
/*  ASSERTVALID_B(b, "toJSBN");
  var j0 = new BigInteger();
  var j1 = new BigInteger();
  var j2 = new BigInteger();
  for(var i = b[0]; i > 0; i--) {
    h$log("i: " + b[i]);
    j2.fromString('' + b[i]);
    j0.lShiftTo(28, j1);
    j1.addTo(j2, j0);
  }
  return j0; */
}
// b = fromJSBN(j) :: BigNat -> JSBN -> Int
// returns length
function h$ghcjsbn_tmp_fromJSBN(b, j) {
  var bl = j.t, i;
  for(i = 0; i < bl; i++) {
    b[i] = j.data[i];
  }
  return bl;
}
// function h$ghcjsbn_divMod_bs(d
// t = b1 % b2 :: BigNat -> BigNat -> BigNat
function h$ghcjsbn_rem_bb(b1, b2) {
  h$ghcjsbn_assertValid_b(b1, "rem_bb b1");
  h$ghcjsbn_assertValid_b(b2, "rem_bb b2");
  var t1 = [], t2 = [];
  h$ghcjsbn_quotRem_bb(t1, t2, b1, b2);
  h$ghcjsbn_assertValid_b(t2, "rem_bb result");
  return t2;
}
// b1 % s :: BigNat -> Word -> Word
function h$ghcjsbn_rem_bw(b, w) {
  h$ghcjsbn_assertValid_b(b, "rem_bw");
  h$ghcjsbn_assertValid_w(w, "rem_bw");
  //  var t1 = [];
  var r = h$ghcjsbn_quotRem_bw([] /* t1 */, b, w);
  h$ghcjsbn_assertValid_w(r, "rem_bw result");
  return r;
//  var a = h$ghcjsbn_tmp_2a;
//  h$ghcjsbn_toBigNat_w(a, w);
//  a[1] = w   & GHCJSBN_MASK;
//  a[2] = w >>> GHCJSBN_BITS;
//  var t1 = []; // , t2 = h$ghcjsbn_tmp_2b;
//  return h$ghcjsbn_quotRem_bw(t1, /* t2 , */ b, a);
//  return t[1] | (t[2] << GHCJSBN_BITS);
}
// b1 / b2 :: BigNat -> BigNat -> BigNat
function h$ghcjsbn_quot_bb(b1, b2) {
  h$ghcjsbn_assertValid_b(b1, "quot_bb b1");
  h$ghcjsbn_assertValid_b(b2, "quot_bb b2");
  var t1 = [], t2 = [];
  h$ghcjsbn_quotRem_bb(t1, t2, b1, b2);
  h$ghcjsbn_assertValid_b(t1, "quot_bb result");
  return t1;
}
/*
// b / s :: BigNat -> Int -> BigNat
function h$ghcjsbn_div_bs(b, w) {
  ASSERTVALID_B(b, "div_bs");
  ASSERTVALID_S(s, "div_bs");
#ifdef GHCJS_ASSERT_INTEGER
  if(s <= 0) {
    throw new Error("h$ghcjsbn_div_bs: divisor must be positive");
  }
#endif
  var a = h$ghcjsbn_tmp_2a;
  a[0] = s &  GHCJSBN_MASK;
  a[1] = s >> GHCJSBN_BITS;
  return h$ghcjsbn_div_bb(t, b, a);
}
*/
// t = b % w :: BigNat -> BigNat -> Word -> Int
// returns length of t
/*
function h$ghcjsbn_div_bw(t, b, w) {
  ASSERTVALID_B(b, "div_bw");
  ASSWRTVALID_W(w, "div_bw");
  var a = h$ghcjsbn_tmp_2a;
 a[0] = w   & GHCJSBN_MASK;
 a[1] = w >>> GHCJSBN_BITS;
  return h$ghcjsbn_div_bb(t, b, a);
}
*/
// b ^ 2 :: BigNat -> BigNat
function h$ghcjsbn_sqr_b(b) {
  h$ghcjsbn_assertValid_b(b, "sqr_b");
  var l = b[0], n = 2 * l, i, c, t = [0];
  for(i = 1; i <= n; i++) t[i] = 0;
  for(i = 0; i < l - 1; i++) {
    c = h$ghcjsbn_mul_limb(i, b, b[i+1],t,2*i,0,1);
    if((t[i + l + 1] += h$ghcjsbn_mul_limb(i+1, b, 2*b[i+1], t, 2*i+1, c, l - i - 1)) >= 0x10000000) {
      t[i + l + 1] -= 0x10000000;
      t[i + l + 2] = 1;
    }
  }
  if(n > 0) t[n] += h$ghcjsbn_mul_limb(i, b, b[i+1], t, 2*i, 0, 1);
  if(t[n] === 0) n--;
  t[0] = n;
  h$ghcjsbn_assertValid_b(t, "sqr_b result");
  return t;
}
// b1 ^ b2 :: BigNat -> BigNat -> BigNat
// returns size of t
function h$ghcjsbn_pow_bb(b1, b2) {
  h$ghcjsbn_assertValid_b(b1, "pow_bb b1");
  h$ghcjsbn_assertValid_b(b2, "pow_bb b2");
  var i, sq = b1, t = [1,1];
  var bits = h$ghcjsbn_nbits_b(b2);
  for(i = 0; i < bits; i++) {
    if(h$ghcjsbn_testBit_b(b2, i)) {
      h$ghcjsbn_mulTo_bb(t, sq);
    }
    sq = h$ghcjsbn_sqr_b(sq);
  }
  return t;
}
// t = b ^ s :: BigNat -> Word -> BigNat
function h$ghcjsbn_pow_bw(b, w) {
  h$ghcjsbn_assertValid_b(b, "pow_bw");
  h$ghcjsbn_assertValid_w(w, "pow_bw");
  var i, sq = b, t = [1,1];
  while(w) {
    if(w&1) h$ghcjsbn_mulTo_bb(t, sq);
    w >>>= 1;
    if(w) {
      sq = h$ghcjsbn_sqr_b(sq);
    }
  }
  h$ghcjsbn_assertValid_b(t, "pow_bw result");
  return t;
}
// w1 ^ w2 :: Word -> Word -> BigNat
function h$ghcjsbn_pow_ww(w1, w2) {
  h$ghcjsbn_assertValid_s(w1, "pow_ww w1");
  h$ghcjsbn_assertValid_s(w2, "pow_ww w2");
  var b = h$ghcjsbn_tmp_2a;
  h$ghcjsbn_toBigNat_w(b, w1);
  var t = h$ghcjsbn_pow_bw(b, w2);
  h$ghcjsbn_assertValid_b(t, "pow_ww result");
  return t;
}
// (b ^ s1) % s2 :: BigNat -> BigNat -> BigNat -> BigNat
function h$ghcjsbn_modPow_bbb(b, s1, s2) {
  throw new Error("modPow_bbb");
}
// (b ^ s1) % s2 :: BigNat -> Int -> Int -> Int
function h$ghcjsbn_modPow_bss(b, s1, s2) {
  throw new Error("modPow_bss");
}
// (s1 ^ s2) % s3 :: Int -> Int -> Int -> Int
function h$ghcjsbn_modPow_sss(s1, s2, s3) {
  throw new Error("modPow_sss");
}
// r = gcd(b1,b2) BigNat -> BigNat -> BigNat
function h$ghcjsbn_gcd_bb(b1, b2) {
  h$ghcjsbn_assertValid_b(b1, "gcd_bb b1");
  h$ghcjsbn_assertValid_b(b2, "gcd_bb b2");
  var r;
  if(h$ghcjsbn_cmp_bb(b1, b2) === 2) {
    r = b1;
    b1 = b2;
    b2 = r;
  }
  while(b1[0] > 0) {
    r = h$ghcjsbn_rem_bb(b2, b1);
    b2 = b1;
    b1 = r;
  }
  h$ghcjsbn_assertValid_b(b2, "gcd_bb result");
  return b2;
}
// gcd(b,s) :: BigNat -> Int -> Int
function h$ghcjsbn_gcd_bs(b, s) {
  throw new Error("h$ghcjsbn_gcd_bs not implemented");
}
// gcd(s1,s2) :: Int -> Int -> Int
function h$ghcjsbn_gcd_ss(s1, s2) {
  h$ghcjsbn_assertValid_s(s1, "gcd_ss s1");
  h$ghcjsbn_assertValid_s(s2, "gcd_ss s2");
  var a, b, r;
  a = s1 < 0 ? -s1 : s1;
  b = s2 < 0 ? -s2 : s2;
  if(b < a) {
    r = a;
    a = b;
    b = r;
  }
  while(a !== 0) {
    r = b % a;
    b = a;
    a = r;
  }
  h$ghcjsbn_assertValid_s(b, "gcd_ss result");
  return b;
}
// gcd(w1,w2) :: Word -> Word -> Word
// fixme negatives are probably wrong here
function h$ghcjsbn_gcd_ww(w1, w2) {
  h$ghcjsbn_assertValid_w(w1, "gcd_ww w1");
  h$ghcjsbn_assertValid_w(w2, "gcd_ww w2");
  var a, b, r;
  a = w1 < 0 ? (w1 + 4294967296) : w1;
  b = w2 < 0 ? (w2 + 4294967296) : w2;
  if(b < a) {
    r = a;
    a = b;
    b = r;
  }
  while(a !== 0) {
    r = b % a;
    b = a;
    a = r;
  }
  b = b|0;
  h$ghcjsbn_assertValid_w(b, "gcd_ww result");
  return b;
}
function h$ghcjsbn_gcd_bw(b, w) {
  h$ghcjsbn_assertValid_b(b, "gcd_bw");
  h$ghcjsbn_assertValid_w(w, "gcd_bw");
  var q = [], r = h$ghcjsbn_quotRem_bw(q, b, w);
  h$ghcjsbn_assertValid_w(r, "gcd_bw r");
  if(r === 0) {
    return b[0] === 0 ? 0 : w;
  } else {
    return h$ghcjsbn_gcd_ww(r, w);
  }
}
// b >> s :: BigNat -> Int -> BigNat
function h$ghcjsbn_shr_b(b, s) {
  h$ghcjsbn_assertValid_b(b, "shr_b");
  h$ghcjsbn_assertValid_s(s, "shr_b");
  if(s < 0) throw new Error("h$ghcjsbn_shr_b: negative operand");
  var i, v1, v2, l = b[0], sl = (s / 28)|0, t = [0];
  l -= sl;
  if(l <= 0) {
    t[0] = 0;
  } else {
    var sb1 = s % 28, sb2 = 28 - sb1, m = (1<<sb1)-1;
    var c = b[sl + 1] >> sb1, v;
    for(i = 1; i < l; i++) {
      v = b[i + sl + 1];
      t[i] = ((v&m) << sb2)|c;
      c = v >> sb1;
    }
    if(c !== 0) {
      t[l] = c;
      t[0] = l;
    } else {
      t[0] = l - 1;
    }
  }
  h$ghcjsbn_assertValid_b(t, "shr_b result");
  return t;
}
// t = b >> s :: BigNat -> BigNat -> Int -> IO ()
function h$ghcjsbn_shrTo_b(t, b, s) {
  h$ghcjsbn_assertValid_b(b, "shrTo_b");
  h$ghcjsbn_assertValid_s(s, "shrTo_b");
  if(s < 0) throw new Error("h$ghcjsbn_shrTo_b: negative operand");
  var i, v1, v2, l = b[0], sl = (s / 28)|0;
  t[0] = 0;
  l -= sl;
  if(l <= 0) {
    t[0] = 0;
  } else {
    var sb1 = s % 28, sb2 = 28 - sb1, m = (1<<sb1)-1;
    var c = b[sl + 1] >> sb1, v;
    for(i = 1; i < l; i++) {
      v = b[i + sl + 1];
      t[i] = ((v&m) << sb2)|c;
      c = v >> sb1;
    }
    if(c !== 0) {
      t[l] = c;
      t[0] = l;
    } else {
      t[0] = l - 1;
    }
  }
  h$ghcjsbn_assertValid_b(t, "shrTo_b result");
}
function h$ghcjsbn_shr_neg_b(b, s) {
  throw new Error ("shr_neg_b not implemented");
}
// b << s :: BigNat -> Int -> BigNat
function h$ghcjsbn_shl_b(b, s) {
  h$ghcjsbn_assertValid_b(b, "shl_b");
  h$ghcjsbn_assertValid_s(s, "shl_b");
  if(s < 0) throw new Error("h$ghcjsbn_shl_b: negative operand");
  var sl = (s / 28)|0;
  var sb1 = s % 28, sb2 = 28 - sb1;
  // mask wrong
  var l = b[0];
  if(l === 0) return h$ghcjsbn_zero_b;
  var c = 0, i, v, m = (1 <<sb1) - 1, t = [0];
  for(i = 1; i <= sl; i++) {
    t[i] = 0;
  }
  for(i = 1; i <= l; i++) {
    v = b[i];
    t[i + sl] = ((v << sb1) & 0xfffffff) | c;
    c = v >> sb2;
  }
  if(c !== 0) {
    t[l+sl+1] = c;
    t[0] = l + sl + 1;
  } else {
    t[0] = l + sl;
  }
  h$ghcjsbn_assertValid_b(t, "shl_b result");
  return t;
}
// t = b << s :: BigNat -> BigNat -> Int -> IO ()
function h$ghcjsbn_shlTo_b(t, b, s) {
  h$ghcjsbn_assertValid_b(b, "shlTo_b");
  h$ghcjsbn_assertValid_s(s, "shlTo_b");
  if(s < 0) throw new Error("h$ghcjsbn_shlTo_b: negative operand");
  var sl = (s / 28)|0;
  var sb1 = s % 28, sb2 = 28 - sb1;
  // mask wrong
  var l = b[0], c = 0, i, v, m = (1 <<sb1) - 1;
  t[0] = 0;
  for(i = 1; i <= sl; i++) {
    t[i] = 0;
  }
  for(i = 1; i <= l; i++) {
    v = b[i];
    t[i + sl] = ((v << sb1) & 0xfffffff) | c;
    c = v >> sb2;
  }
  if(c !== 0) {
    t[l+sl+1] = c;
    t[0] = l + sl + 1;
  } else {
    t[0] = l + sl;
  }
  h$ghcjsbn_assertValid_b(t, "shlTo_b result");
}
// t = b >> (GHCJSBN_BITS * s) :: BigNat -> BigNat -> Int
function h$ghcjsbn_shrTo_limbs_b(t, b, s) {
  h$ghcjsbn_assertValid_b(b, "shrTo_limbs_b");
  h$ghcjsbn_assertValid_s(s, "shrTo_limbs_b");
  if(s < 0) throw new Error("h$ghcjsbn_shrTo_limbs_b: negative operand");
  var l = b[0], l1 = l - s, i;
  if(l1 < 1) {
    t[0] = 0;
  } else {
    t[0] = l1;
    for(i = 1; i <= l1; i++) t[i] = b[i+s];
  }
  h$ghcjsbn_assertValid_b(t, "shrTo_limbs_b result");
}
// t = b << (GHCJSBN_BITS * s) :: BigNat -> BigNat -> Int
function h$ghcjsbn_shlTo_limbs_b(t, b, s) {
  h$ghcjsbn_assertValid_b(b, "shlTo_limbs_b");
  h$ghcjsbn_assertValid_s(s, "shlTo_limbs_b");
  if(s < 0) throw new Error("h$ghcjsbn_shlTo_limbs_b: negative operand");
  var l = b[0], l1 = l + s, i;
  if(l === 0) {
    t[0] = 0;
  } else {
    t[0] = l1;
    for(i = 1; i <= s; i++) t[i] = 0;
    for(i = s+1; i <= l1; i++) t[i] = b[i-s];
  }
  h$ghcjsbn_assertValid_b(t, "shlTo_limbs_b result");
}
function h$ghcjsbn_nbits_b(b) {
  h$ghcjsbn_assertValid_b(b, "nbits_b");
  var l = b[0], c = 0, s, t;
  if(l === 0) {
    return 0;
  } else {
    var r = ((l-1)*28) + h$ghcjsbn_nbits_s(b[l]);
    h$ghcjsbn_assertValid_s(r, "nbits_b result");
    return r;
  }
}
function h$ghcjsbn_nbits_s(s) {
  h$ghcjsbn_assertValid_s(s, "nbits_s");
  var c = 1, t;
  if((t = s >>> 16) != 0) { s = t; c += 16; }
  if((t = s >> 8) != 0) { s = t; c += 8; }
  if((t = s >> 4) != 0) { s = t; c += 4; }
  if((t = s >> 2) != 0) { s = t; c += 2; }
  if((t = s >> 1) != 0) { s = t; c += 1; }
  h$ghcjsbn_assertValid_s(c, "nbits_s result");
  return c;
}
// BigNat -> Word -> String
function h$ghcjsbn_showBase(b, base) {
  h$ghcjsbn_assertValid_b(b, "showBase");
  h$ghcjsbn_assertValid_s(base, "showBase");
  if(h$ghcjsbn_cmp_bb(b, h$ghcjsbn_zero_b) === 1) {
    return "0";
  } else {
    return h$ghcjsbn_showBase_rec(b, base, Math.log(base), 0);
  }
}
function h$ghcjsbn_showBase_rec(b, base, logBase, pad) {
  var bits = h$ghcjsbn_nbits_b(b), r;
  // h$log("[" + b.join(",") + "] bits: " + bits);
  if(h$ghcjsbn_cmp_bb(b, h$ghcjsbn_two31_b) === 0) {
    // convert short numbers to int and show in base
    var ti = h$ghcjsbn_toInt_b(b);
    // h$log("############# got base limb: " + ti);
    r = ti === 0 ? "" : ti.toString(base);
  } else {
    // divide and conquer for long numbers
    var digits = Math.floor(bits * 0.6931471805599453 / logBase);
    var d2 = Math.round(digits/2), p, q = [], r = [];
    p = h$ghcjsbn_pow_ww(base, d2);
    h$ghcjsbn_quotRem_bb(q, r, b, p);
    r = h$ghcjsbn_showBase_rec(q, base, logBase, 0) +
        h$ghcjsbn_showBase_rec(r, base, logBase, d2);
  }
  var rl = r.length;
  if(rl < pad) {
    while(rl <= pad-8) { r = "00000000" + r; rl += 8; }
    switch(pad-rl) {
    case 1: r = "0" + r; break;
    case 2: r = "00" + r; break;
    case 3: r = "000" + r; break;
    case 4: r = "0000" + r; break;
    case 5: r = "00000" + r; break;
    case 6: r = "000000" + r; break;
    case 7: r = "0000000" + r; break;
    }
  }
  return r;
}
// BigNat -> String (decimal)
function h$ghcjsbn_show(b) {
  return h$ghcjsbn_showBase(b, 10);
}
// BigNat -> String
function h$ghcjsbn_showHex(b) {
  return h$ghcjsbn_showBase(b, 16);
}
function h$ghcjsbn_readBigNat(str) {
  var m = /^\s*(\d+)\s*/.exec(str);
  if(!m) return [0];
  return h$ghcjsbn_readBigNatDigits(m[1]);
}
// the string may only contain digits
function h$ghcjsbn_readBigNatDigits(digits) {
  if(digits.length > 9) {
    var h = (digits.length / 2)|0,
        l = digits.substring(0, h),
        r = digits.substring(h),
        m = h$ghcjsbn_pow_ww(10, r.length),
        bl = h$ghcjsbn_readBigNatDigits(l),
        br = h$ghcjsbn_readBigNatDigits(r);
    return h$ghcjsbn_add_bb(h$ghcjsbn_mul_bb(bl, m), br);
  } else {
    return h$ghcjsbn_mkBigNat_w(parseInt(digits));
  }
}
function h$ghcjsbn_readInteger(str) {
  var m = /^\s*-?([0-9]+)\s*/.exec(str);
  if(!m) return null;
  var digits = m[1];
  var isNegative = str.indexOf('-') !== -1;
  if(digits.length <= 9) {
    if(isNegative) {
      return (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziSzh_con_e, (-parseInt(digits, 10))));;
    } else {
      return (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziSzh_con_e, (parseInt(digits, 10))));;
    }
  } else {
    var bn = h$ghcjsbn_readBigNat(digits);
    if(isNegative) {
      return (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziJnzh_con_e, (bn)));;
    } else {
      return (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziJpzh_con_e, (bn)));;
    }
  }
}
// s = b[l - 1];
// normalize a number to length l by stripping unused leading digits
/*
function h$ghcjsbn_normalize(b, l) {
  var d = b.length - l;
  while(d--) b.pop();
}

// normalize a number by stripping leading zeroes
function h$ghcjsbn_normalize0(b) {
  var l = b.length;
  while(b[--l] === 0) b.pop();
}
*/
// t = b :: BigNat -> BigNat -> Int, returns length of t
function h$ghcjsbn_copy(t, b) {
  h$ghcjsbn_assertValid_b(b, "copy");
  var l = b[0];
  for(var i = 0; i <= l; i++) {
    t[i] = b[i];
  }
  return l;
}
// BigNat -> Int -> Bool
// test if bit n is set in b (least significant bit is 0)
function h$ghcjsbn_testBit_b(b, n) {
  h$ghcjsbn_assertValid_b(b, "testBit_b");
  h$ghcjsbn_assertValid_s(n, "testBit_b");
  var limb = (n / 28)|0;
  if(limb >= b[0]) {
    return false;
  } else {
    var d = b[limb];
    var bit = n - (28 * limb);
    return (b[limb] & (1 << bit)) !== 0;
  }
}
function h$ghcjsbn_popCount_b(b) {
  h$ghcjsbn_assertValid_b(b, "popCount_b");
  var c = 0, l = b[0];
  while(l > 0) {
    c += h$popCnt32(b[l--]);
  }
  return c;
}
// t = b1 ^ b2 :: BigNat -> BigNat -> BigNat -> Int
// returns length of t
function h$ghcjsbn_xor_bb(b1, b2) {
  h$ghcjsbn_assertValid_b(b1, "xor_bb b1");
  h$ghcjsbn_assertValid_b(b2, "xor_bb b2");
  var i, lmin, lmax, blmax, l1 = b1[0], l2 = b2[0], t = [0];
  if(l1 <= l2) {
    lmin = l1;
    lmax = l2;
    blmax = b2;
  } else {
    lmin = l2;
    lmax = l1;
    blmax = b1;
  }
  for(i = 1; i <= lmin; i++) {
    t[i] = b1[i] ^ b2[i];
  }
  for(i = lmin + 1; i <= lmax; i++) {
    t[i] = blmax[i];
  }
  while(lmax > 0 && t[lmax] === 0) lmax--;
  t[0] = lmax;
  h$ghcjsbn_assertValid_b(t, "xor_bb result");
  return t;
}
// b1 | b2 :: BigNat -> BigNat -> BigNat
function h$ghcjsbn_or_bb(b1, b2) {
  h$ghcjsbn_assertValid_b(b1, "or_bb b1");
  h$ghcjsbn_assertValid_b(b2, "or_bb b2");
  var i, lmin, lmax, blmax, l1 = b1[0], l2 = b2[0], t = [0];
  if(l1 <= l2) {
    lmin = l1;
    lmax = l2;
    blmax = b2;
  } else {
    lmin = l2;
    lmax = l1;
    blmax = b1;
  }
  for(i = 1; i <= lmin; i++) {
    t[i] = b1[i] | b2[i];
  }
  for(i = lmin + 1; i <= lmax; i++) {
    t[i] = blmax[i];
  }
  t[0] = lmax;
  h$ghcjsbn_assertValid_b(t, "or_bb result");
  return t;
}
// b1 & b2 :: BigNat -> BigNat -> BigNat
function h$ghcjsbn_and_bb(b1, b2) {
  h$ghcjsbn_assertValid_b(b1, "and_bb b1");
  h$ghcjsbn_assertValid_b(b2, "and_bb b2");
  var i, lmin, l1 = b1[0], l2 = b2[0], t = [0];
  lmin = l1 <= l2 ? l1 : l2;
  for(i = 1; i <= lmin; i++) {
    t[i] = b1[i] & b2[i];
  }
  while(lmin > 0 && t[lmin] === 0) lmin--;
  t[0] = lmin;
  h$ghcjsbn_assertValid_b(t, "and_bb result");
  return t;
}
// b1 & (~b2) :: BigNat -> BigNat -> BigNat
// fixme is this one correct?
function h$ghcjsbn_andn_bb(b1, b2) {
  h$ghcjsbn_assertValid_b(b1, "andn_bb b1");
  h$ghcjsbn_assertValid_b(b2, "andn_bb b2");
  var i, lmin, l1 = b1[0], l2 = b2[0], t = [0];
  if(l1 <= l2) {
    for(i = 0; i <= l1; i++) t[i] = b1[i] & (~b2[i]);
  } else {
    for(i = 0; i <= l2; i++) t[i] = b1[i] & (~b2[i]);
    for(i = l2+1; i <= l1; i++) t[i] = b1[i];
  }
  while(l1 > 0 && t[l1] === 0) l1--;
  t[0] = l1;
  h$ghcjsbn_assertValid_b(t, "andn_bb result");
  return t;
}
function h$ghcjsbn_toInt_b(b) {
  h$ghcjsbn_assertValid_b(b, "toInt_b");
  var bl = b[0], r;
  if(bl >= 2) {
    r = (b[2] << 28) | b[1];
  } else if(bl === 1) {
    r = b[1];
  } else {
    r = 0;
  }
  h$ghcjsbn_assertValid_s(r, "toInt_b result");
  return r;
}
function h$ghcjsbn_toWord_b(b) {
  h$ghcjsbn_assertValid_b(b, "toWord_b");
  var bl = b[0], w;
  if(bl >= 2) {
    w = (b[2] << 28) | b[1];
  } else if(bl === 1) {
    w = b[1];
  } else {
    w = 0;
  }
  h$ghcjsbn_assertValid_w(w, "toWord_b result");
  return w;
}
var h$integer_bigNatToWord64 = h$ghcjsbn_toWord64_b;
var h$integer_word64ToBigNat = h$ghcjsbn_mkBigNat_ww; // fixme?
function h$ghcjsbn_toWord64_b(b) {
  h$ghcjsbn_assertValid_b(b, "toWord64_b");
  var len = b[0], w1, w2;
  if(len < 2) {
    w2 = 0;
    w1 = (len === 1) ? b[1] : 0;
  } else {
    w1 = b[1] | (b[2] << 28);
    if(len === 2) {
      w2 = b[2] >>> 4;
    } else {
      w2 = (b[2] >>> 4) | (b[3] << 24);
    }
  }
  h$ghcjsbn_assertValid_w(w2, "toWord64_b result w2");
  h$ghcjsbn_assertValid_w(w1, "toWord64_b result w1");
  { h$ret1 = (w1); return (w2); };
}
// BigNat -> Int -> IO ()
function h$ghcjsbn_toBigNat_s(b, s) {
  h$ghcjsbn_assertValid_s(s, "toBigNat_s");
  if(s < 0) {
    throw new Error("h$ghcjsbn_toBigNat_s: negative operand");
  }
  if(s === 0) {
    b[0] = 0;
  } else if(s <= 0xfffffff) {
    b[0] = 1;
    b[1] = s;
  } else {
    b[0] = 2;
    b[1] = s & 0xfffffff;
    b[2] = s >> 0xfffffff;
  }
  h$ghcjsbn_assertValid_b(b, "toBigNat_s result");
}
// BigNat -> Word -> IO ()
function h$ghcjsbn_toBigNat_w(b, w) {
  h$ghcjsbn_assertValid_w(w, "toBigNat_w");
  if(w === 0) {
    b[0] = 0;
  } else if(w > 0 && w <= 0xfffffff) {
    b[0] = 1;
    b[1] = w;
  } else {
    b[0] = 2;
    b[1] = w & 0xfffffff;
    b[2] = w >>> 28;
  }
  h$ghcjsbn_assertValid_b(b, "toBigNat_w result");
}
function h$ghcjsbn_mkBigNat_w(w) {
  h$ghcjsbn_assertValid_w(w, "mkBigNat_w");
  var r;
  if(w === 0) r = h$ghcjsbn_zero_b;
  else if(w === 1) r = h$ghcjsbn_one_b;
  else if(w > 0 && w <= 0xfffffff) r = [1,w];
  else r = [2, w & 0xfffffff, w >>> 28];
  h$ghcjsbn_assertValid_b(r, "mkBigNat_w result");
  // ASSERTVALID_B(h$ghcjsbn_zero_b, "mkBigNat_w zero");
  return r;
}
function h$ghcjsbn_mkBigNat_ww(hw, lw) {
  h$ghcjsbn_assertValid_w(hw, "mkBigNat_ww hw");
  h$ghcjsbn_assertValid_w(lw, "mkBigNat_ww lw");
  var r;
  if(hw === 0) r = h$ghcjsbn_mkBigNat_w(lw);
  else {
    var w1 = lw & 0xfffffff;
    var w2 = (lw >>> 28) | ((hw << 4) & 0xfffffff);
    var w3 = hw >>> 24;
    if(w3 === 0) {
      r = [2, w1, w2];
    } else {
      r = [3, w1, w2, w3];
    }
  }
  h$ghcjsbn_assertValid_b(r, "mkBigNat_ww result");
  return r;
}
// fixme remove after reboot
var h$ghcjsbn_toBigNat_ww = h$ghcjsbn_mkBigNat_ww;
/* fixme re-enable after reboot
function h$ghcjsbn_toBigNat_ww(b, hw, lw) {
  ASSERTVALID_W(hw, "toBigNat_ww hw");
  ASSERTVALID_W(lw, "toBigNat_ww lw");
  if(hw === 0) h$ghcjsbn_toBigNat_w(b, lw);
  else {
    var w1 = lw & GHCJSBN_MASK;
    var w2 = (lw >>> GHCJSBN_BITS) | ((hw << 4) & GHCJSBN_MASK);
    var w3 = hw >>> 24;
    if(w3 === 0) {
      r[0] = 2;
      r[1] = w1;
      r[2] = w2;
    } else {
      r[0] = 3;
      r[1] = w1;
      r[2] = w2;
      r[3] = w3;
    }
  }
}
*/
// fixme remove later
var h$integer_mkInteger = h$ghcjsbn_mkInteger;
function h$ghcjsbn_mkInteger(nonNeg, xs) {
  // fixme write proper optimized version
  var r = [0], s = 0, t;
  while(((xs).f === h$ghczmprimZCGHCziTypesziZC_con_e)) {
    t = h$ghcjsbn_shl_b(h$ghcjsbn_mkBigNat_w(((typeof(((xs).d1)) === 'number')?(((xs).d1)):(((xs).d1)).d1)), s);
    h$ghcjsbn_addTo_bb(r, t);
    s += 31;
    xs = ((xs).d2);
  }
  if(nonNeg) {
    if(h$ghcjsbn_cmp_bb(r, h$ghcjsbn_two31_b) === 0) {
      return (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziSzh_con_e, (h$ghcjsbn_toInt_b(r))));;
    } else {
      return (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziJpzh_con_e, (r)));;
    }
  } else {
    var c = h$ghcjsbn_cmp_bb(r, h$ghcjsbn_two31_b);
    if(c === 2) {
      return (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziJnzh_con_e, (r)));;
    } else if(c === 1) {
      return h$ghcjsbn_negTwo31_i;
    } else {
      return (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziSzh_con_e, (-h$ghcjsbn_toInt_b(r))));;
    }
  }
/*  var r = h$ghcjsbn_mkBigNat_w(0), l = 0, s = 0, y, t;
  while(IS_CONS(xs)) {
    l++;
    y  = UNWRAP_NUMBER(CONS_HEAD(xs));
    r[++l] = (y << s | c) & GHCJSBN_MASK;
    c  = y >>> s;
    xs = CONS_TAIL(xs);
    s  += 3;
    l++;
    if(s > GHCJSBN_BITS) {
      s  -= GHCJSBN_BITS;
      r[++l] = c & GHCJSBN_MASK;
      c >>= GHCJSBN_BITS;
    }
  }
  if(c !== 0) r[++l] =
  while(
  if(l === 0) {
    return MK_INTEGER_S(0);
  } else if(l === 1) {

  } else if(l === 2) {

  } */
}
// BigNat -> Int -> Int
function h$ghcjsbn_indexBigNat(b, i) {
  h$ghcjsbn_assertValid_b(b, "indexBigNat");
  h$ghcjsbn_assertValid_s(i, "indexBigNat");
  var bl = b[0];
  return i >= bl ? 0 : b[i+1];
}
// BigNat -> Word -> Int (Ordering)
function h$ghcjsbn_cmp_bw(b, w) {
  h$ghcjsbn_assertValid_b(b, "cmp_bw");
  h$ghcjsbn_assertValid_w(w, "cmp_bw");
  var w1 = w & 0xfffffff, w2 = w >>> 28, bl = b[0];
  if(w2 === 0) {
    if(bl === 0) {
      return w1 > 0 ? 0 : 1;
    } else if(bl === 1) {
      var bw = b[1];
      return bw > w1 ? 2 : (bw === w1 ? 1 : 0);
    } else {
      return 2;
    }
  } else {
    if(bl < 2) {
      return 0;
    } else if(bl > 2) {
      return 2;
    } else {
      var bw1 = b[1], bw2 = b[2];
      return (bw2 > w2) ? 2
                        : (bw2 < w2 ? 0
                                    : (bw1 > w1 ? 2
                                                : (bw1 < w1 ? 0
                                                            : 1)));
    }
  }
}
/*
function h$ghcjsbn_gt_bw(b, w) {
  var r = h$ghcjsbn_gt_bw0(b,w);
  h$log("gt_bw result: " + r);
  return r;
}
*/
function h$ghcjsbn_gt_bw(b, w) {
  h$ghcjsbn_assertValid_b(b, "gt_bw");
  h$ghcjsbn_assertValid_w(w, "gt_bw");
  var bl = b[0];
  if(bl > 2) return true;
  else if(bl === 0) return false;
  else if(bl === 1) return w >= 0 && b[1] > w;
  else { // bl === 2
    var wh = w >>> 28, wl = w & 0xfffffff, b2 = b[2];
    // var r = (wh > b2 || ((wh === b2) && wl > b[1]));
    // h$log("r: " + r + " " + wh + " " + wl + " " );
    return (b2 > wh || ((wh === b2) && b[1] > wl));
  }
}
// BigNat -> BigNat -> Bool
function h$ghcjsbn_eq_bb(b1, b2) {
  h$ghcjsbn_assertValid_b(b1, "eq_bb");
  h$ghcjsbn_assertValid_b(b2, "eq_bb");
  var bl1 = b1[0], bl2 = b2[0];
  if(bl1 !== bl2) {
    return false;
  } else {
    for(var i = bl1; i >= 1; i--) {
      var bw1 = b1[i], bw2 = b2[i];
      if(bw1 !== bw2) return false;
    }
  }
  return true; // GHCJSBN_EQ;
}
// BigNat -> BigNat -> Bool
function h$ghcjsbn_neq_bb(b1, b2) {
  h$ghcjsbn_assertValid_b(b1, "neq_bb");
  h$ghcjsbn_assertValid_b(b2, "neq_bb");
  var bl1 = b1[0], bl2 = b2[0];
  if(bl1 !== bl2) {
    return true;
  } else {
    for(var i = bl1; i >= 1; i--) {
      var bw1 = b1[i], bw2 = b2[i];
      if(bw1 !== bw2) return true;
    }
  }
  return false;
}
// BigNat -> BigNat -> Bool
/*
function h$ghcjsbn_eq_bw(b, w) {
  var r = h$ghcjsbn_eq_bw0(b, w);
  return r;
}
*/
function h$ghcjsbn_eq_bw(b, w) {
  h$ghcjsbn_assertValid_b(b, "eq_bw");
  h$ghcjsbn_assertValid_w(w, "eq_bw");
  var w1 = w & 0xfffffff, w2 = w >>> 28, bl = b[0];
  if(w2 === 0) {
    if(w1 === 0) {
      return bl === 0;
    } else {
      return bl === 1 && b[1] === w;
    }
  } else {
    return bl === 2 && b[1] === w1 && b[2] === w2;
  }
}
// BigNat -> Bool
function h$ghcjsbn_isZero_b(b) {
  h$ghcjsbn_assertValid_b(b, "isZero_b");
  return b[0] === 0;
}
// BigNat -> Int
function h$ghcjsbn_isNull_b(b) {
  return b[0] === -1;
}
// 1 << n
function h$ghcjsbn_bitBigNat(n) {
  if(n < 0) {
    throw new Error("bitBigNat: argument must be positive");
  }
  if(n === 0) {
    r = h$ghcjsbn_one_b;
  } else if(n < 28) {
    r = [1, 1 << n];
  } else {
    var l = (n / 28)|0;
    var r = [l+1];
    for(var i = 1; i<= l; i++) r[i] = 0;
    r[l+1] = 1 << (n - (28 * l));
  }
  h$ghcjsbn_assertValid_b(r, "bitBigNat result");
  return r;
}
// Integer -> Int
// assumes argument is strictly positive
function h$ghcjsbn_integerLog2(i) {
  h$ghcjsbn_assertValid_i(i, "integerLog2");
/*  if(h$ghcjsbn_cmp_ii(i, h$ghcjsbn_zero_i) !== GHCJSBN_GT) {
    throw new Error("integerLog2: argument must be positive");
  } */
  if(((i).f === h$integerzmgmpZCGHCziIntegerziTypeziSzh_con_e)) {
    return h$ghcjsbn_nbits_s(((i).d1));
  } else {
    return h$ghcjsbn_nbits_b(((i).d1));
  }
}
// Integer -> Int
// returns negation of result if integer is exactly a power of two
function h$ghcjsbn_integerLog2IsPowerOf2(i) {
  h$ghcjsbn_assertValid_i(i, "integerLog2IsPowerOf2");
/*  if(h$ghcjbn_cmp_ii(i, h$ghcjsbn_zero_i) !== GHCJSBN_GT) {
    throw new Error("integerLog2IsPowerOf2: argument must be positive");
  } */
  var nb;
  if(((i).f === h$integerzmgmpZCGHCziIntegerziTypeziSzh_con_e)) {
    var sd = ((i).d1);
    h$ghcjsbn_assertValid_s(sd, "integerLog2IsPowerOf2 sd");
    nb = h$ghcjsbn_nbits_s(sd);
    return ((sd === 1 << nb) ? -nb : nb);
  } else {
    var bd = ((i).d1);
    h$ghcjsbn_assertValid_b(bd, "integerLog2IsPowerOf2 bd");
    nb = h$ghcjsbn_nbits_b(bd);
    var i, bl = (nb / 28) | 0, lb = nb - 28 * bl, l = bd[bl+1];
    if(l !== (1 << lb)) return nb;
    for(i = bl; i >= 1; i--) {
      if(bd[i] !== 0) return nb;
    }
    return -nb;
  }
}
// BigNat? -> Int
function h$ghcjsbn_isValid_b(b) {
  if(!Array.isArray(b)) return 0;
  if(b.length < 1) return 0;
  var bl = b[0], w;
  if(b.length < (bl+1)) return 0;
  for(var i = 0; i <= bl; i++) {
    w = b[i];
    if(typeof w !== 'number' || (w & 0xfffffff) !== w) return 0;
  }
  return 1;
}
// BigNat -> Integer
function h$ghcjsbn_toInteger_b(b) {
  h$ghcjsbn_assertValid_b(b, "toInteger_b");
  if(h$ghcjsbn_cmp_bb(b, h$ghcjsbn_two31_b) === 0) {
    return (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziSzh_con_e, (h$ghcjsbn_toInt_b(b))));;
  } else {
    return (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziJpzh_con_e, (b)));;
  }
}
// BigNat -> Integer
function h$ghcjsbn_toNegInteger_b(b) {
  h$ghcjsbn_assertValid_b(b, "toNegInteger_b");
  var c = h$ghcjsbn_cmp_bb(b, h$ghcjsbn_two31_b);
  if(c === 0) {
    return (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziSzh_con_e, (-h$ghcjsbn_toInt_b(b))));;
  } else if(c === 1) {
    return h$ghcjsbn_negTwo31_i;
  } else {
    return (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziJnzh_con_e, (b)));;
  }
}
// BigNat? -> Int
// (can be called with invalid bignat)
function h$ghcjsbn_sizeof_b(b) {
  if(b.length < 1) return 0;
  var bl = b[0];
  return Math.ceil((bl * 28) / 32);
}
// extract a word from a BigNat
function h$ghcjsbn_index_b(b, w) {
  throw new Error("index_b");
  h$ghcjsbn_assertValid_b(b, "index_b");
  h$ghcjsbn_assertValid_w(w, "index_b");
  var wbit = 32*w, len = b[0], limb = (wbit / 28) | 0, lb = wbit - (limb * 28);
  var r = b[limb+1] >>> lb;
/*  if() {

  } */
  h$ghcjsbn_assertValid_w(r, "index_b result");
}
// Bool -> BigNat -> Double
function h$ghcjsbn_toDouble_b(nonNeg, b) {
  throw new Error("toDouble_b");
}
function h$ghcjsbn_byteArrayToBigNat(ba, len) {
  throw new Error("h$ghcjsbn_byteArrayToBigNat not yet implemented");
}
function h$ghcjsbn_importBigNatFromAddr(a_d, a_o, len, msbf) {
  throw new Error("h$ghcjsbn_importBigNatFromAddr not yet implemented");
}
function h$ghcjsbn_importBigNatFromByteArray(ba, ofs, len, msbf) {
  throw new Error("h$ghcjsbn_importBigNatFromByteArray not yet implemented");
}
//////////////////////////////////////////////////////////////////////////////
// fixme move to primop places later
var h$integer_int64ToInteger = h$ghcjsbn_toInteger_s64;
function h$ghcjsbn_toInteger_s64(s_a, s_b) {
  h$ghcjsbn_assertValid_s(s_a, "toInteger_s64 s_a");
  h$ghcjsbn_assertValid_s(s_b, "toInteger_s64 s_b");
  if(s_a === 0) {
    if(s_b >= 0) {
      return (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziSzh_con_e, (s_b)));;
    } else {
      return (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziJpzh_con_e, (h$ghcjsbn_mkBigNat_w(s_b))));;
    }
  } else if(s_a === -1) {
    if(s_b < 0) {
      return (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziSzh_con_e, (s_b)));;
    } else if(s_b === 0) {
      return (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziJnzh_con_e, (h$ghcjsbn_mkBigNat_ww(1,0))));;
    } else {
      return (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziJnzh_con_e, (h$ghcjsbn_mkBigNat_w(((~s_b)+1)|0))));;
    }
  } else if(s_a > 0) {
    return (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziJpzh_con_e, (h$ghcjsbn_mkBigNat_ww(s_a, s_b))));;
  } else {
    if(s_b === 0) { // zero should be correct!
      return (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziJnzh_con_e, (h$ghcjsbn_mkBigNat_ww(((~s_a)+1)|0, 0))));;
    } else {
      return (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziJnzh_con_e, (h$ghcjsbn_mkBigNat_ww((~s_a)|0, ((~s_b)+1)|0))));;
    }
    /*
     if(s_b === 0) { // zero should be correct!
      return MK_INTEGER_Jn(h$ghcjsbn_mkBigNat_ww(((~s_a)+1)|0, 0));
    } else {
      return MK_INTEGER_Jn(h$ghcjsbn_mkBigNat_ww(~s_a, ((~s_b)+1)|0));
    } */
  }
}
function h$decodeDoubleInt64(d) {
  h$ghcjsbn_assertValid_d(d, "DoubleDecode_Int64");
  if(isNaN(d)) {
    // RETURN_UBX_TUP4(null, -1572864, 0, 972);
    { h$ret1 = (-1572864); h$ret2 = (0); return (972); };
  }
  h$convertDouble[0] = d;
  var i0 = h$convertInt[0], i1 = h$convertInt[1];
  var exp = (i1&2146435072)>>>20;
  var ret1, ret2 = i0, ret3;
  if(exp === 0) { // denormal or zero
    if((i1&2147483647) === 0 && ret2 === 0) {
      ret1 = 0;
      ret3 = 0;
    } else {
      h$convertDouble[0] = d*9007199254740992;
      i1 = h$convertInt[1];
      ret1 = (i1&1048575)|1048576;
      ret2 = h$convertInt[0];
      ret3 = ((i1&2146435072)>>>20)-1128;
    }
  } else {
    ret3 = exp-1075;
    ret1 = (i1&1048575)|1048576;
  }
  // negate mantissa for negative input
  if(d < 0) {
    if(ret2 === 0) {
      ret1 = ((~ret1) + 1) | 0;
      // ret2 = 0;
    } else {
      ret1 = ~ret1;
      ret2 = ((~ret2) + 1) | 0;
    }
  }
  // prim ubx tup returns don't return the first value!
  { h$ret1 = (ret1); h$ret2 = (ret2); return (ret3); };
}
// fixme remove this once rebooted
function h$primop_DoubleDecode_Int64Op(d) {
  h$ghcjsbn_assertValid_d(d, "DoubleDecode_Int64");
  if(isNaN(d)) {
    // RETURN_UBX_TUP4(null, -1572864, 0, 972);
    { h$ret1 = (-1572864); h$ret2 = (0); h$ret3 = (972); return (null); };
  }
  h$convertDouble[0] = d;
  var i0 = h$convertInt[0], i1 = h$convertInt[1];
  var exp = (i1&2146435072)>>>20;
  var ret1, ret2 = i0, ret3;
  if(exp === 0) { // denormal or zero
    if((i1&2147483647) === 0 && ret2 === 0) {
      ret1 = 0;
      ret3 = 0;
    } else {
      h$convertDouble[0] = d*9007199254740992;
      i1 = h$convertInt[1];
      ret1 = (i1&1048575)|1048576;
      ret2 = h$convertInt[0];
      ret3 = ((i1&2146435072)>>>20)-1128;
    }
  } else {
    ret3 = exp-1075;
    ret1 = (i1&1048575)|1048576;
  }
  // negate mantissa for negative input
  if(d < 0) {
    if(ret2 === 0) {
      ret1 = ((~ret1) + 1) | 0;
      // ret2 = 0;
    } else {
      ret1 = ~ret1;
      ret2 = ((~ret2) + 1) | 0;
    }
  }
  // prim ubx tup returns don't return the first value!
  { h$ret1 = (ret1); h$ret2 = (ret2); h$ret3 = (ret3); return (null); };
}
function h$ghcjsbn_encodeDouble_b(pos, b, e) {
  h$ghcjsbn_assertValid_b(b, "encodeDouble_b");
  h$ghcjsbn_assertValid_s(e, "encodeDouble_b");
  if(e >= 972) {
    return pos ? Infinity : -Infinity;
  }
  var ls = 1, bl = b[0], i, r = b[bl], mul = 1 << 28, rmul = 1/mul, s = 1;
  for(i = bl-1; i >= 1; i--) {
/*    if(e > GHCJSBN_BITS) {
      e -= GHCJSBN_BITS;
      s *= rmul;
      r  = r + s * b[i];
    } else { */
      r = r * mul + s * b[i];
//    }
  }
  // h$log("remaning exp: " + e);
  if(e > 600) {
    r = r * Math.pow(2, e-600) * Math.pow(2,600);
  } else if(e < -600) {
    r = r * Math.pow(2, e+600) * Math.pow(2,-600);
  } else {
    r = r * Math.pow(2, e);
  }
  h$ghcjsbn_assertValid_d(r, "encodeDouble_b result");
  return pos ? r : -r;
}
function h$ghcjsbn_toDouble_b(nonNeg, b) {
  return h$ghcjsbn_encodeDouble_b(nonNeg, b, 0);
}
// fixme
var h$ghcjsbn_encodeDouble_i = h$ghcjsbn_encodeDouble_s;
function h$ghcjsbn_encodeDouble_s(m, e) {
  h$ghcjsbn_assertValid_s(m, "encodeDouble_s m");
  h$ghcjsbn_assertValid_s(e, "encodeDouble_s e");
  var r = m * Math.pow(2, e);
  h$ghcjsbn_assertValid_d(r, "encodeDouble_s result");
  return r;
}
/* Copyright (C) 1991-2017 Free Software Foundation, Inc.
   This file is part of the GNU C Library.

   The GNU C Library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2.1 of the License, or (at your option) any later version.

   The GNU C Library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public
   License along with the GNU C Library; if not, see
   <http://www.gnu.org/licenses/>.  */
/* This header is separate from features.h so that the compiler can
   include it implicitly at the start of every compilation.  It must
   not itself include <features.h> or any other header that includes
   <features.h> because the implicit include comes before any feature
   test macros that may be defined in a source file before it first
   explicitly includes a system header.  GCC knows the name of this
   header in order to preinclude it.  */
/* glibc's intent is to support the IEC 559 math functionality, real
   and complex.  If the GCC (4.9 and later) predefined macros
   specifying compiler intent are available, use them to determine
   whether the overall intent is to support these features; otherwise,
   presume an older compiler has intent to support these features and
   define these macros by default.  */
/* wchar_t uses Unicode 8.0.0.  Version 8.0 of the Unicode Standard is
   synchronized with ISO/IEC 10646:2014, plus Amendment 1 (published
   2015-05-15).  */
/* We do not support C11 <threads.h>.  */
function h$dom$sendXHR(xhr, d, cont) {
    var clear;
    var error = function () {
        clear(); cont(2);
    };
    var abort = function () {
        clear(); cont(1);
    };
    var load = function () {
        clear(); cont(0);
    };
    clear = function () {
        xhr.removeEventListener('error', error);
        xhr.removeEventListener('abort', abort);
        xhr.removeEventListener('load', load);
    }
    xhr.addEventListener('error', error);
    xhr.addEventListener('abort', abort);
    xhr.addEventListener('load', load);
    if(d) {
 xhr.send(d);
    } else {
 xhr.send();
    }
}
/* Copyright (C) 1991-2017 Free Software Foundation, Inc.
   This file is part of the GNU C Library.

   The GNU C Library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2.1 of the License, or (at your option) any later version.

   The GNU C Library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public
   License along with the GNU C Library; if not, see
   <http://www.gnu.org/licenses/>.  */
/* This header is separate from features.h so that the compiler can
   include it implicitly at the start of every compilation.  It must
   not itself include <features.h> or any other header that includes
   <features.h> because the implicit include comes before any feature
   test macros that may be defined in a source file before it first
   explicitly includes a system header.  GCC knows the name of this
   header in order to preinclude it.  */
/* glibc's intent is to support the IEC 559 math functionality, real
   and complex.  If the GCC (4.9 and later) predefined macros
   specifying compiler intent are available, use them to determine
   whether the overall intent is to support these features; otherwise,
   presume an older compiler has intent to support these features and
   define these macros by default.  */
/* wchar_t uses Unicode 8.0.0.  Version 8.0 of the Unicode Standard is
   synchronized with ISO/IEC 10646:2014, plus Amendment 1 (published
   2015-05-15).  */
/* We do not support C11 <threads.h>.  */
// values defined in Gen2.ClosureInfo
// thread status
/*
 * low-level heap object manipulation macros
 */
// GHCJS.Prim.JSVal
// GHCJS.Prim.JSException
// Exception dictionary for JSException
// SomeException
// GHC.Ptr.Ptr
// GHC.Integer.GMP.Internals
// Data.Maybe.Maybe
// #define HS_NOTHING h$nothing
// Data.List
// Data.Text
// Data.Text.Lazy
// black holes
// can we skip the indirection for black holes?
// resumable thunks
// general deconstruction
// retrieve  a numeric value that's possibly stored as an indirection
// generic lazy values
// generic data constructors and selectors
// unboxed tuple returns
// #define RETURN_UBX_TUP1(x) return x;
function h$createWebSocket(url, protocols) {
  return new WebSocket(url, protocols);
}
/*
   this must be called before the websocket has connected,
   typically synchronously after creating the socket
 */
function h$openWebSocket(ws, mcb, ccb, c) {
  if(ws.readyState !== 0) {
    throw new Error("h$openWebSocket: unexpected readyState, socket must be CONNECTING");
  }
  ws.lastError = null;
  ws.onopen = function() {
    if(mcb) {
      ws.onmessage = mcb;
    }
    if(ccb || mcb) {
      ws.onclose = function(ce) {
        if(ws.onmessage) {
          h$release(ws.onmessage);
          ws.onmessage = null;
        }
        if(ccb) {
          h$release(ccb);
          ccb(ce);
        }
      };
    };
    ws.onerror = function(err) {
      ws.lastError = err;
      if(ws.onmessage) {
        h$release(ws.onmessage);
        ws.onmessage = null;
      }
      ws.close();
    };
    c(null);
  };
  ws.onerror = function(err) {
    if(ccb) h$release(ccb);
    if(mcb) h$release(mcb);
    ws.onmessage = null;
    ws.close();
    c(err);
  };
}
function h$closeWebSocket(status, reason, ws) {
  ws.onerror = null;
  if(ws.onmessage) {
    h$release(ws.onmessage);
    ws.onmessage = null;
  }
  ws.close(status, reason);
}
/* Copyright (C) 1991-2017 Free Software Foundation, Inc.
   This file is part of the GNU C Library.

   The GNU C Library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2.1 of the License, or (at your option) any later version.

   The GNU C Library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public
   License along with the GNU C Library; if not, see
   <http://www.gnu.org/licenses/>.  */
/* This header is separate from features.h so that the compiler can
   include it implicitly at the start of every compilation.  It must
   not itself include <features.h> or any other header that includes
   <features.h> because the implicit include comes before any feature
   test macros that may be defined in a source file before it first
   explicitly includes a system header.  GCC knows the name of this
   header in order to preinclude it.  */
/* glibc's intent is to support the IEC 559 math functionality, real
   and complex.  If the GCC (4.9 and later) predefined macros
   specifying compiler intent are available, use them to determine
   whether the overall intent is to support these features; otherwise,
   presume an older compiler has intent to support these features and
   define these macros by default.  */
/* wchar_t uses Unicode 8.0.0.  Version 8.0 of the Unicode Standard is
   synchronized with ISO/IEC 10646:2014, plus Amendment 1 (published
   2015-05-15).  */
/* We do not support C11 <threads.h>.  */
// values defined in Gen2.ClosureInfo
// thread status
/*
 * low-level heap object manipulation macros
 */
// GHCJS.Prim.JSVal
// GHCJS.Prim.JSException
// Exception dictionary for JSException
// SomeException
// GHC.Ptr.Ptr
// GHC.Integer.GMP.Internals
// Data.Maybe.Maybe
// #define HS_NOTHING h$nothing
// Data.List
// Data.Text
// Data.Text.Lazy
// black holes
// can we skip the indirection for black holes?
// resumable thunks
// general deconstruction
// retrieve  a numeric value that's possibly stored as an indirection
// generic lazy values
// generic data constructors and selectors
// unboxed tuple returns
// #define RETURN_UBX_TUP1(x) return x;
/*
   convert an array to a Haskell list, wrapping each element in a
   JSVal constructor
 */
function h$fromArray(a) {
    var r = h$ghczmprimZCGHCziTypesziZMZN;
    for(var i=a.length-1;i>=0;i--) r = (h$c2(h$ghczmprimZCGHCziTypesziZC_con_e, ((h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (a[i])))), (r)));
    return a;
}
/*
   convert an array to a Haskell list. No additional wrapping of the
   elements is performed. Only use this when the elements are directly
   usable as Haskell heap objects (numbers, boolean) or when the
   array elements have already been appropriately wrapped
 */
function h$fromArrayNoWrap(a) {
    var r = h$ghczmprimZCGHCziTypesziZMZN;
    for(var i=a.length-1;i>=0;i--) r = (h$c2(h$ghczmprimZCGHCziTypesziZC_con_e, (a[i]), (r)));
    return a;
}
/*
   convert a list of JSVal to an array. the list must have been fully forced,
   not just the spine.
 */
function h$listToArray(xs) {
    var a = [], i = 0;
    while(((xs).f === h$ghczmprimZCGHCziTypesziZC_con_e)) {
 a[i++] = ((((xs).d1)).d1);
 xs = ((xs).d2);
    }
    return a;
}
function h$listToArrayWrap(xs) {
    return (h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (h$listToArray(xs))));
}
/* Copyright (C) 1991-2017 Free Software Foundation, Inc.
   This file is part of the GNU C Library.

   The GNU C Library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2.1 of the License, or (at your option) any later version.

   The GNU C Library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public
   License along with the GNU C Library; if not, see
   <http://www.gnu.org/licenses/>.  */
/* This header is separate from features.h so that the compiler can
   include it implicitly at the start of every compilation.  It must
   not itself include <features.h> or any other header that includes
   <features.h> because the implicit include comes before any feature
   test macros that may be defined in a source file before it first
   explicitly includes a system header.  GCC knows the name of this
   header in order to preinclude it.  */
/* glibc's intent is to support the IEC 559 math functionality, real
   and complex.  If the GCC (4.9 and later) predefined macros
   specifying compiler intent are available, use them to determine
   whether the overall intent is to support these features; otherwise,
   presume an older compiler has intent to support these features and
   define these macros by default.  */
/* wchar_t uses Unicode 8.0.0.  Version 8.0 of the Unicode Standard is
   synchronized with ISO/IEC 10646:2014, plus Amendment 1 (published
   2015-05-15).  */
/* We do not support C11 <threads.h>.  */
function h$animationFrameCancel(h) {
    if(h.handle) window.cancelAnimationFrame(h.handle);
    if(h.callback) {
        h$release(h.callback)
        h.callback = null;
    }
}
function h$animationFrameRequest(h) {
    h.handle = window.requestAnimationFrame(function(ts) {
        var cb = h.callback;
        if(cb) {
         h$release(cb);
         h.callback = null;
         cb(ts);
        }
    });
}
/* Copyright (C) 1991-2017 Free Software Foundation, Inc.
   This file is part of the GNU C Library.

   The GNU C Library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2.1 of the License, or (at your option) any later version.

   The GNU C Library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public
   License along with the GNU C Library; if not, see
   <http://www.gnu.org/licenses/>.  */
/* This header is separate from features.h so that the compiler can
   include it implicitly at the start of every compilation.  It must
   not itself include <features.h> or any other header that includes
   <features.h> because the implicit include comes before any feature
   test macros that may be defined in a source file before it first
   explicitly includes a system header.  GCC knows the name of this
   header in order to preinclude it.  */
/* glibc's intent is to support the IEC 559 math functionality, real
   and complex.  If the GCC (4.9 and later) predefined macros
   specifying compiler intent are available, use them to determine
   whether the overall intent is to support these features; otherwise,
   presume an older compiler has intent to support these features and
   define these macros by default.  */
/* wchar_t uses Unicode 8.0.0.  Version 8.0 of the Unicode Standard is
   synchronized with ISO/IEC 10646:2014, plus Amendment 1 (published
   2015-05-15).  */
/* We do not support C11 <threads.h>.  */
function h$exportValue(fp1a,fp1b,fp2a,fp2b,o) {
  var e = { fp1a: fp1a
          , fp1b: fp1b
          , fp2a: fp2a
          , fp2b: fp2b
          , released: false
          , root: o
          , _key: -1
          };
  h$retain(e);
  return e;
}
function h$derefExport(fp1a,fp1b,fp2a,fp2b,e) {
  if(!e || typeof e !== 'object') return null;
  if(e.released) return null;
  if(fp1a !== e.fp1a || fp1b !== e.fp1b ||
     fp2a !== e.fp2a || fp2b !== e.fp2b) return null;
  return e.root;
}
function h$releaseExport(e) {
  h$release(e);
  e.released = true;
  e.root = null;
}
/* Copyright (C) 1991-2017 Free Software Foundation, Inc.
   This file is part of the GNU C Library.

   The GNU C Library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2.1 of the License, or (at your option) any later version.

   The GNU C Library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public
   License along with the GNU C Library; if not, see
   <http://www.gnu.org/licenses/>.  */
/* This header is separate from features.h so that the compiler can
   include it implicitly at the start of every compilation.  It must
   not itself include <features.h> or any other header that includes
   <features.h> because the implicit include comes before any feature
   test macros that may be defined in a source file before it first
   explicitly includes a system header.  GCC knows the name of this
   header in order to preinclude it.  */
/* glibc's intent is to support the IEC 559 math functionality, real
   and complex.  If the GCC (4.9 and later) predefined macros
   specifying compiler intent are available, use them to determine
   whether the overall intent is to support these features; otherwise,
   presume an older compiler has intent to support these features and
   define these macros by default.  */
/* wchar_t uses Unicode 8.0.0.  Version 8.0 of the Unicode Standard is
   synchronized with ISO/IEC 10646:2014, plus Amendment 1 (published
   2015-05-15).  */
/* We do not support C11 <threads.h>.  */
// values defined in Gen2.ClosureInfo
// thread status
/*
 * low-level heap object manipulation macros
 */
// GHCJS.Prim.JSVal
// GHCJS.Prim.JSException
// Exception dictionary for JSException
// SomeException
// GHC.Ptr.Ptr
// GHC.Integer.GMP.Internals
// Data.Maybe.Maybe
// #define HS_NOTHING h$nothing
// Data.List
// Data.Text
// Data.Text.Lazy
// black holes
// can we skip the indirection for black holes?
// resumable thunks
// general deconstruction
// retrieve  a numeric value that's possibly stored as an indirection
// generic lazy values
// generic data constructors and selectors
// unboxed tuple returns
// #define RETURN_UBX_TUP1(x) return x;
/*
 * Support code for the Data.JSString module. This code presents a JSString
 * as a sequence of code points and hides the underlying encoding ugliness of
 * the JavaScript strings.
 *
 * Use Data.JSString.Raw for direct access to the JSThis makes the operations more expen
 */
/*
 * Some workarounds here for JS engines that do not support proper
 * code point access
 */
var h$jsstringEmpty = (h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, ('')));
var h$jsstringHead, h$jsstringTail, h$jsstringCons,
    h$jsstringSingleton, h$jsstringSnoc, h$jsstringUncons,
    h$jsstringIndex, h$jsstringUncheckedIndex,
    h$jsstringTake, h$jsstringDrop, h$jsstringTakeEnd, h$jsstringDropEnd;
var h$fromCodePoint;
if(String.prototype.fromCodePoint) {
    h$fromCodePoint = String.fromCodePoint;
} else {
    // polyfill from https://github.com/mathiasbynens/String.fromCodePoint (MIT-license)
    h$fromCodePoint =
      (function() {
          var stringFromCharCode = String.fromCharCode;
          var floor = Math.floor;
          return function(_) {
              var MAX_SIZE = 0x4000;
              var codeUnits = [];
              var highSurrogate;
              var lowSurrogate;
              var index = -1;
              var length = arguments.length;
              if (!length) {
                  return '';
              }
              var result = '';
              while (++index < length) {
                  var codePoint = Number(arguments[index]);
                  if (
                      !isFinite(codePoint) || // `NaN`, `+Infinity`, or `-Infinity`
                      codePoint < 0 || // not a valid Unicode code point
                      codePoint > 0x10FFFF || // not a valid Unicode code point
                      floor(codePoint) != codePoint // not an integer
                  ) {
                      throw RangeError('Invalid code point: ' + codePoint);
                  }
                  if (codePoint <= 0xFFFF) { // BMP code point
                      codeUnits.push(codePoint);
                  } else { // Astral code point; split in surrogate halves
                      // https://mathiasbynens.be/notes/javascript-encoding#surrogate-formulae
                      codePoint -= 0x10000;
                      highSurrogate = (codePoint >> 10) + 0xD800;
                      lowSurrogate = (codePoint % 0x400) + 0xDC00;
                      codeUnits.push(highSurrogate, lowSurrogate);
                  }
                  if (index + 1 == length || codeUnits.length > MAX_SIZE) {
                      result += stringFromCharCode.apply(null, codeUnits);
                      codeUnits.length = 0;
                  }
              }
              return result;
          }
      })();
}
if(String.prototype.codePointAt) {
    h$jsstringSingleton = function(ch) {
        ;
 return String.fromCodePoint(ch);
    }
    h$jsstringHead = function(str) {
        ;
 var cp = str.codePointAt(0);
 return (cp === undefined) ? -1 : (cp|0);
    }
    h$jsstringTail = function(str) {
        ;
 var l = str.length;
 if(l===0) return null;
 var ch = str.codePointAt(0);
 if(ch === undefined) return null;
 // string length is at least two if ch comes from a surrogate pair
 return str.substr(((ch)>=0x10000)?2:1);
    }
    h$jsstringCons = function(ch, str) {
        ;
 return String.fromCodePoint(ch)+str;
    }
    h$jsstringSnoc = function(str, ch) {
        ;
 return str+String.fromCodePoint(ch);
    }
    h$jsstringUncons = function(str) {
        ;
 var l = str.length;
 if(l===0) {
          { h$ret1 = (null); return (-1); };
        }
 var ch = str.codePointAt(0);
        if(ch === undefined) {
     { h$ret1 = (null); return (-1); };
        }
        { h$ret1 = (str.substr(((ch)>=0x10000)?2:1)); return (ch); };
    }
    // index is the first part of the character
    h$jsstringIndex = function(i, str) {
        ;
 var ch = str.codePointAt(i);
 if(ch === undefined) return -1;
 return ch;
    }
    h$jsstringUncheckedIndex = function(i, str) {
        ;
 return str.codePointAt(i);
    }
} else {
    h$jsstringSingleton = function(ch) {
        ;
 return (((ch)>=0x10000)) ? String.fromCharCode(((((ch)-0x10000)>>>10)+0xDC00), (((ch)&0x3FF)+0xD800))
                               : String.fromCharCode(ch);
    }
    h$jsstringHead = function(str) {
        ;
 var l = str.length;
 if(l===0) return -1;
 var ch = str.charCodeAt(0);
 if(((ch|1023)===0xDBFF)) {
     return (l>1) ? ((((ch)-0xD800)<<10)+(str.charCodeAt(1))-9216) : -1;
 } else {
     return ch;
 }
    }
    h$jsstringTail = function(str) {
        ;
 var l = str.length;
 if(l===0) return null;
 var ch = str.charCodeAt(0);
 if(((ch|1023)===0xDBFF)) {
     return (l>1)?str.substr(2):null;
 } else return str.substr(1);
    }
    h$jsstringCons = function(ch, str) {
        ;
 return ((((ch)>=0x10000)) ? String.fromCharCode(((((ch)-0x10000)>>>10)+0xDC00), (((ch)&0x3FF)+0xD800))
                                : String.fromCharCode(ch))
                                + str;
    }
    h$jsstringSnoc = function(str, ch) {
        ;
 return str + ((((ch)>=0x10000)) ? String.fromCharCode(((((ch)-0x10000)>>>10)+0xDC00), (((ch)&0x3FF)+0xD800))
                                      : String.fromCharCode(ch));
    }
    h$jsstringUncons = function(str) {
        ;
 var l = str.length;
 if(l===0) {
          { h$ret1 = (null); return (-1); };
        }
 var ch = str.charCodeAt(0);
 if(((ch|1023)===0xDBFF)) {
   if(l > 1) {
        { h$ret1 = (str.substr(2)); return (((((ch)-0xD800)<<10)+(str.charCodeAt(1))-9216)); };
   } else {
       { h$ret1 = (null); return (-1); };
   }
 } else {
      { h$ret1 = (str.substr(1)); return (ch); };
 }
    }
    // index is the first part of the character
    h$jsstringIndex = function(i, str) {
        // TRACE_JSSTRING("(no codePointAt) index: " + i + " '" + str + "'");
 var ch = str.charCodeAt(i);
 if(ch != ch) return -1; // NaN test
 return (((ch|1023)===0xDBFF)) ? ((((ch)-0xD800)<<10)+(str.charCodeAt(i+1))-9216) : ch;
    }
    h$jsstringUncheckedIndex = function(i, str) {
        ;
 var ch = str.charCodeAt(i);
 return (((ch|1023)===0xDBFF)) ? ((((ch)-0xD800)<<10)+(str.charCodeAt(i+1))-9216) : ch;
    }
}
function h$jsstringPack(xs) {
    var r = '', i = 0, a = [], c;
    while(((xs).f === h$ghczmprimZCGHCziTypesziZC_con_e)) {
 c = ((xs).d1);
 a[i++] = ((typeof(c) === 'number')?(c):(c).d1);
 if(i >= 60000) {
     r += h$fromCodePoint.apply(null, a);
     a = [];
     i = 0;
 }
 xs = ((xs).d2);
    }
    if(i > 0) r += h$fromCodePoint.apply(null, a);
    ;
    return r;
}
function h$jsstringPackReverse(xs) {
    var a = [], i = 0, c;
    while(((xs).f === h$ghczmprimZCGHCziTypesziZC_con_e)) {
 c = ((xs).d1);
 a[i++] = ((typeof(c) === 'number')?(c):(c).d1);
 xs = ((xs).d2);
    }
    if(i===0) return '';
    var r = h$jsstringConvertArray(a.reverse());
    ;
    return r;
}
function h$jsstringPackArray(arr) {
    ;
    return h$jsstringConvertArray(arr);
}
function h$jsstringPackArrayReverse(arr) {
    ;
    return h$jsstringConvertArray(arr.reverse());
}
function h$jsstringConvertArray(arr) {
    if(arr.length < 60000) {
 return h$fromCodePoint.apply(null, arr);
    } else {
 var r = '';
 for(var i=0; i<arr.length; i+=60000) {
     r += h$fromCodePoint.apply(null, arr.slice(i, i+60000));
 }
 return r;
    }
}
function h$jsstringInit(str) {
    ;
    var l = str.length;
    if(l===0) return null;
    var ch = str.charCodeAt(l-1);
    var o = ((ch|1023)===0xDFFF)?2:1;
    var r = str.substr(0, l-o);
    return r;
}
function h$jsstringLast(str) {
    ;
    var l = str.length;
    if(l===0) return -1;
    var ch = str.charCodeAt(l-1);
    if(((ch|1023)===0xDFFF)) {
 return (l>1) ? ((((str.charCodeAt(l-2))-0xD800)<<10)+(ch)-9216) : -1;
    } else return ch;
}
// index is the last part of the character
function h$jsstringIndexR(i, str) {
    ;
    if(i < 0 || i > str.length) return -1;
    var ch = str.charCodeAt(i);
    return (((ch|1023)===0xDFFF)) ? ((((str.charCodeAt(i-1))-0xD800)<<10)+(ch)-9216) : ch;
}
function h$jsstringNextIndex(i, str) {
    ;
    return i + (((str.charCodeAt(i)|1023)===0xDBFF)?2:1);
}
function h$jsstringTake(n, str) {
    ;
    if(n <= 0) return '';
    var i = 0, l = str.length, ch;
    if(n >= l) return str;
    while(n--) {
 ch = str.charCodeAt(i++);
 if(((ch|1023)===0xDBFF)) i++;
 if(i >= l) return str;
    }
    return str.substr(0,i);
}
function h$jsstringDrop(n, str) {
    ;
    if(n <= 0) return str;
    var i = 0, l = str.length, ch;
    if(n >= l) return '';
    while(n--) {
 ch = str.charCodeAt(i++);
 if(((ch|1023)===0xDBFF)) i++;
 if(i >= l) return str;
    }
    return str.substr(i);
}
function h$jsstringSplitAt(n, str) {
  ;
  if(n <= 0) {
    { h$ret1 = (str); return (""); };
  } else if(n >= str.length) {
    { h$ret1 = (""); return (str); };
  }
  var i = 0, l = str.length, ch;
  while(n--) {
    ch = str.charCodeAt(i++);
    if(((ch|1023)===0xDBFF)) i++;
    if(i >= l) {
      { h$ret1 = (""); return (str); };
    }
  }
  { h$ret1 = (str.substr(i)); return (str.substr(0,i)); };
}
function h$jsstringTakeEnd(n, str) {
    ;
    if(n <= 0) return '';
    var l = str.length, i = l-1, ch;
    if(n >= l) return str;
    while(n-- && i > 0) {
 ch = str.charCodeAt(i--);
 if(((ch|1023)===0xDFFF)) i--;
    }
    return (i<0) ? str : str.substr(i+1);
}
function h$jsstringDropEnd(n, str) {
    ;
    if(n <= 0) return str;
    var l = str.length, i = l-1, ch;
    if(n >= l) return '';
    while(n-- && i > 0) {
 ch = str.charCodeAt(i--);
 if(((ch|1023)===0xDFFF)) i--;
    }
    return (i<0) ? '' : str.substr(0,i+1);
}
function h$jsstringIntercalate(x, ys) {
    ;
    var a = [], i = 0;
    while(((ys).f === h$ghczmprimZCGHCziTypesziZC_con_e)) {
 if(i) a[i++] = x;
 a[i++] = ((((ys).d1)).d1);
 ys = ((ys).d2);
    }
    return a.join('');
}
function h$jsstringIntersperse(ch, ys) {
    ;
    var i = 0, l = ys.length, j = 0, a = [], ych;
    if(((ch)>=0x10000)) {
 var ch1 = ((((ch)-0x10000)>>>10)+0xDC00), ch2 = (((ch)&0x3FF)+0xD800);
 while(j < l) {
     if(i) {
  a[i++] = ch1;
  a[i++] = ch2;
     }
     ych = ys.charCodeAt(j++);
     a[i++] = ych;
     if(((ych|1023)===0xDBFF)) a[i++] = ys.charCodeAt(j++);
 }
    } else {
 while(j < l) {
     if(i) a[i++] = ch;
     ych = ys.charCodeAt(j++);
     a[i++] = ych;
     if(((ych|1023)===0xDBFF)) a[i++] = ys.charCodeAt(j++);
 }
    }
    return h$jsstringConvertArray(a);
}
function h$jsstringConcat(xs) {
    ;
    var a = [], i = 0;
    while(((xs).f === h$ghczmprimZCGHCziTypesziZC_con_e)) {
 a[i++] = ((((xs).d1)).d1);
 xs = ((xs).d2);
    }
    return a.join('');
}
var h$jsstringStripPrefix, h$jsstringStripSuffix,
    h$jsstringIsPrefixOf, h$jsstringIsSuffixOf,
    h$jsstringIsInfixOf;
if(String.prototype.startsWith) {
    h$jsstringStripPrefix = function(p, x) {
 ;
 if(x.startsWith(p)) {
     return (h$c1(h$baseZCGHCziBaseziJust_con_e, ((h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (x.substr(p.length)))))));
 } else {
     return h$baseZCGHCziBaseziNothing;
 }
    }
    h$jsstringIsPrefixOf = function(p, x) {
 ;
 return x.startsWith(p);
    }
} else {
    h$jsstringStripPrefix = function(p, x) {
 ;
 if(x.indexOf(p) === 0) { // this has worse complexity than it should
     return (h$c1(h$baseZCGHCziBaseziJust_con_e, ((h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (x.substr(p.length)))))));
 } else {
   return h$baseZCGHCziBaseziNothing;
 }
    }
    h$jsstringIsPrefixOf = function(p, x) {
 ;
 return x.indexOf(p) === 0; // this has worse complexity than it should
    }
}
if(String.prototype.endsWith) {
    h$jsstringStripSuffix = function(s, x) {
 ;
 if(x.endsWith(s)) {
     return (h$c1(h$baseZCGHCziBaseziJust_con_e, ((h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (x.substr(0,x.length-s.length)))))));
 } else {
   return h$baseZCGHCziBaseziNothing;
 }
    }
    h$jsstringIsSuffixOf = function(s, x) {
 ;
 return x.endsWith(s);
    }
} else {
    h$jsstringStripSuffix = function(s, x) {
 ;
 var i = x.lastIndexOf(s); // this has worse complexity than it should
 var l = x.length - s.length;
 if(i !== -1 && i === l) {
     return (h$c1(h$baseZCGHCziBaseziJust_con_e, ((h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (x.substr(0,l)))))));
 } else {
   return h$baseZCGHCziBaseziNothing;
 }
    }
      h$jsstringIsSuffixOf = function(s, x) {
 ;
        var i = x.lastIndexOf(s); // this has worse complexity than it should
 return i !== -1 && i === x.length - s.length;
    }
}
if(String.prototype.includes) {
    h$jsstringIsInfixOf = function(i, x) {
        ;
 return x.includes(i);
    }
} else {
    h$jsstringIsInfixOf = function(i, x) {
        ;
 return x.indexOf(i) !== -1; // this has worse complexity than it should
    }
}
function h$jsstringCommonPrefixes(x, y) {
    ;
    var lx = x.length, ly = y.length, i = 0, cx;
    var l = lx <= ly ? lx : ly;
    if(lx === 0 || ly === 0 || x.charCodeAt(0) !== y.charCodeAt(0)) {
      return h$baseZCGHCziBaseziNothing;
    }
    while(++i<l) {
 cx = x.charCodeAt(i);
 if(cx !== y.charCodeAt(i)) {
     if(((cx|1023)===0xDFFF)) i--;
     break;
 }
    }
  if(i===0) return h$baseZCGHCziBaseziNothing;
    return (h$c1(h$baseZCGHCziBaseziJust_con_e, ((h$c3(h$ghczmprimZCGHCziTupleziZLz2cUz2cUZR_con_e,((h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, ((i===lx)?x:((i===ly)?y:x.substr(0,i)))))),((i===lx) ? h$jsstringEmpty : (h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (x.substr(i))))),((i===ly) ? h$jsstringEmpty : (h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (y.substr(i))))))))));
}
function h$jsstringBreakOn(b, x) {
    ;
    var i = x.indexOf(b);
    if(i===-1) {
        { h$ret1 = (""); return (x); };
    }
    if(i===0) {
        { h$ret1 = (x); return (""); };
    }
    { h$ret1 = (x.substr(i)); return (x.substr(0,i)); };
}
function h$jsstringBreakOnEnd(b, x) {
    ;
    var i = x.lastIndexOf(b);
  if(i===-1) {
    { h$ret1 = (x); return (""); };
    }
  i += b.length;
    { h$ret1 = (x.substr(i)); return (x.substr(0,i)); };
}
function h$jsstringBreakOnAll1(n, b, x) {
    ;
    var i = x.indexOf(b, n);
    if(i===0) {
       { h$ret1 = (""); h$ret2 = (x); return (b.length); };
    }
    if(i===-1) {
       { h$ret1 = (null); h$ret2 = (null); return (-1); };
    }
    { h$ret1 = (x.substr(0,i)); h$ret2 = (x.substr(i)); return (i+b.length); };
}
function h$jsstringBreakOnAll(pat, src) {
    ;
    var a = [], i = 0, n = 0, r = h$ghczmprimZCGHCziTypesziZMZN, pl = pat.length;
    while(true) {
 var x = src.indexOf(pat, n);
 if(x === -1) break;
 a[i++] = (h$c2(h$ghczmprimZCGHCziTupleziZLz2cUZR_con_e,((h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (src.substr(0,x))))),((h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (src.substr(x)))))));
 n = x + pl;
    }
    while(--i >= 0) r = (h$c2(h$ghczmprimZCGHCziTypesziZC_con_e, (a[i]), (r)));
    return r;
}
function h$jsstringSplitOn1(n, p, x) {
    ;
    var i = x.indexOf(p, n);
    if(i === -1) {
        { h$ret1 = (null); return (-1); };
    }
    var r1 = (i==n) ? "" : x.substr(n, i-n);
    { h$ret1 = (r1); return (i + p.length); };
}
function h$jsstringSplitOn(p, x) {
    ;
    var a = x.split(p);
    var r = h$ghczmprimZCGHCziTypesziZMZN, i = a.length;
    while(--i>=0) r = (h$c2(h$ghczmprimZCGHCziTypesziZC_con_e, ((h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (a[i])))), (r)));
    return r;
}
// returns -1 for end of input, start of next token otherwise
// word in h$ret1
// this function assumes that there are no whitespace characters >= 0x10000
function h$jsstringWords1(n, x) {
    ;
    var m = n, s = n, l = x.length;
    if(m >= l) return -1;
    // skip leading spaces
    do {
 if(m >= l) return -1;
    } while(h$isSpace(x.charCodeAt(m++)));
    // found start of word
    s = m - 1;
    while(m < l) {
 if(h$isSpace(x.charCodeAt(m++))) {
     // found end of word
            var r1 = (m-s<=1) ? "" : x.substr(s,m-s-1);
            { h$ret1 = (r1); return (m); };
 }
    }
    // end of string
    if(s < l) {
        var r1 = s === 0 ? x : x.substr(s);
        { h$ret1 = (r1); return (m); };
    }
    { h$ret1 = (null); return (-1); };
}
function h$jsstringWords(x) {
    ;
    var a = null, i = 0, n, s = -1, m = 0, w, l = x.length, r = h$ghczmprimZCGHCziTypesziZMZN;
    outer:
    while(m < l) {
 // skip leading spaces
 do {
     if(m >= l) { s = m; break outer; }
 } while(h$isSpace(x.charCodeAt(m++)));
 // found start of word
 s = m - 1;
 while(m < l) {
     if(h$isSpace(x.charCodeAt(m++))) {
  // found end of word
  w = (m-s<=1) ? h$jsstringEmpty
                             : (h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (x.substr(s,m-s-1))));
  if(i) a[i++] = w; else { a = [w]; i = 1; }
  s = m;
  break;
     }
 }
    }
    // end of string
    if(s !== -1 && s < l) {
 w = (h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (s === 0 ? x : x.substr(s))));
 if(i) a[i++] = w; else { a = [w]; i = 1; }
    }
    // build resulting list
    while(--i>=0) r = (h$c2(h$ghczmprimZCGHCziTypesziZC_con_e, (a[i]), (r)));
    return r;
}
// returns -1 for end of input, start of next token otherwise
// line in h$ret1
function h$jsstringLines1(n, x) {
    ;
    var m = n, l = x.length;
    if(n >= l) return -1;
    while(m < l) {
 if(x.charCodeAt(m++) === 10) {
     // found newline
     if(n > 0 && n === l-1) return -1; // it was the last character
            var r1 = (m-n<=1) ? "" : x.substr(n,m-n-1);
            { h$ret1 = (r1); return (m); };
 }
    }
    // end of string
    { h$ret1 = (x.substr(n)); return (m); };
}
function h$jsstringLines(x) {
    ;
    var a = null, m = 0, i = 0, l = x.length, s = 0, r = h$ghczmprimZCGHCziTypesziZMZN, w;
    if(l === 0) return h$ghczmprimZCGHCziTypesziZMZN;
    outer:
    while(true) {
 s = m;
 do {
     if(m >= l) break outer;
 } while(x.charCodeAt(m++) !== 10);
 w = (m-s<=1) ? h$jsstringEmpty : (h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (x.substr(s,m-s-1))));
 if(i) a[i++] = w; else { a = [w]; i = 1; }
    }
    if(s < l) {
 w = (h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (x.substr(s))));
 if(i) a[i++] = w; else { a = [w]; i = 1; }
    }
    while(--i>=0) r = (h$c2(h$ghczmprimZCGHCziTypesziZC_con_e, (a[i]), (r)));
    return r;
}
function h$jsstringGroup(x) {
    ;
    var xl = x.length;
    if(xl === 0) return h$ghczmprimZCGHCziTypesziZMZN;
    var i = xl-1, si, ch, s=xl, r=h$ghczmprimZCGHCziTypesziZMZN;
    var tch = x.charCodeAt(i--);
    if(((tch|1023)===0xDFFF)) tch = ((((x.charCodeAt(i--))-0xD800)<<10)+(tch)-9216);
    while(i >= 0) {
 si = i;
 ch = x.charCodeAt(i--);
 if(((ch|1023)===0xDFFF)) {
     ch = ((((x.charCodeAt(i--))-0xD800)<<10)+(ch)-9216);
 }
 if(ch != tch) {
     tch = ch;
     r = (h$c2(h$ghczmprimZCGHCziTypesziZC_con_e, ((h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (x.substr(si+1,s-si))))), (r)));
     s = si;
 }
    }
    return (h$c2(h$ghczmprimZCGHCziTypesziZC_con_e, ((h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (x.substr(0,s+1))))), (r)));
}
function h$jsstringChunksOf1(n, s, x) {
    ;
    var m = s, c = 0, l = x.length, ch;
    if(n <= 0 || l === 0 || s >= l) return -1
    while(++m < l && ++c < n) {
 ch = x.charCodeAt(m);
 if(((ch|1023)===0xDBFF)) ++m;
    }
    var r1 = (m >= l && s === c) ? x : x.substr(s,m-s);
    { h$ret1 = (r1); return (m); };
}
function h$jsstringChunksOf(n, x) {
    ;
    var l = x.length;
    if(l===0 || n <= 0) return h$ghczmprimZCGHCziTypesziZMZN;
    if(l <= n) return (h$c2(h$ghczmprimZCGHCziTypesziZC_con_e, ((h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (x)))), (h$ghczmprimZCGHCziTypesziZMZN)));
    var a = [], i = 0, s = 0, ch, m = 0, c, r = h$ghczmprimZCGHCziTypesziZMZN;
    while(m < l) {
 s = m;
 c = 0;
 while(m < l && ++c <= n) {
     ch = x.charCodeAt(m++);
     if(((ch|1023)===0xDBFF)) ++m;
 }
 if(c) a[i++] = x.substr(s, m-s);
    }
    while(--i>=0) r = (h$c2(h$ghczmprimZCGHCziTypesziZC_con_e, ((h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (a[i])))), (r)));
    return r;
}
function h$jsstringCount(pat, src) {
    ;
    var i = 0, n = 0, pl = pat.length, sl = src.length;
    while(i<sl) {
 i = src.indexOf(pat, i);
 if(i===-1) break;
 n++;
 i += pl;
    }
    return n;
}
function h$jsstringReplicate(n, str) {
    ;
    if(n === 0 || str == '') return '';
    if(n === 1) return str;
    var r = '';
    do {
 if(n&1) r+=str;
        str+=str;
        n >>= 1;
    } while(n > 1);
    return r+str;
}
// this does not deal with combining diacritics, Data.Text does not either
var h$jsstringReverse;
if(Array.from) {
    h$jsstringReverse = function(str) {
 ;
 return Array.from(str).reverse().join('');
    }
} else {
    h$jsstringReverse = function(str) {
 ;
 var l = str.length, a = [], o = 0, i = 0, c, c1, s = '';
 while(i < l) {
     c = str.charCodeAt(i);
     if(((c|1023)===0xDBFF)) {
  a[i] = str.charCodeAt(i+1);
  a[i+1] = c;
  i += 2;
     } else a[i++] = c;
     if(i-o > 60000) {
  s = String.fromCharCode.apply(null, a.reverse()) + s;
  o = -i;
  a = [];
     }
 }
 return (i===0) ? s : String.fromCharCode.apply(null,a.reverse()) + s;
    }
}
function h$jsstringUnpack(str) {
    ;
    var r = h$ghczmprimZCGHCziTypesziZMZN, i = str.length-1, c;
    while(i >= 0) {
 c = str.charCodeAt(i--);
 if(((c|1023)===0xDFFF)) c = ((((str.charCodeAt(i--))-0xD800)<<10)+(c)-9216)
 r = (h$c2(h$ghczmprimZCGHCziTypesziZC_con_e, (c), (r)));
    }
    return r;
}
function h$jsstringDecInteger(val) {
  ;
  if(((val).f === h$integerzmgmpZCGHCziIntegerziTypeziSzh_con_e)) {
    return '' + ((val).d1);
  } else if(((val).f === h$integerzmgmpZCGHCziIntegerziTypeziJpzh_con_e)) {
    return h$ghcjsbn_showBase(((val).d1), 10);
  } else {
    return '-' + h$ghcjsbn_showBase(((val).d1), 10);
  }
}
function h$jsstringDecI64(hi,lo) {
    ;
    var lo0 = (lo < 0) ? lo+4294967296:lo;
    if(hi < 0) {
 if(hi === -1) return ''+(lo0-4294967296);
 lo0 = 4294967296 - lo0;
 var hi0 = -1 - hi;
 var x0 = hi0 * 967296;
 var x1 = (lo0 + x0) % 1000000;
 var x2 = hi0*4294+Math.floor((x0+lo0-x1)/1000000);
 return '-' + x2 + h$jsstringDecIPadded6(x1);
    } else {
 if(hi === 0) return ''+lo0;
 var x0 = hi * 967296;
 var x1 = (lo0 + x0) % 1000000;
 var x2 = hi*4294+Math.floor((x0+lo0-x1)/1000000);
 return '' + x2 + h$jsstringDecIPadded6(x1);
    }
}
function h$jsstringDecW64(hi,lo) {
    ;
    var lo0 = (lo < 0) ? lo+4294967296 : lo;
    if(hi === 0) return ''+lo0;
    var hi0 = (hi < 0) ? hi+4294967296 : hi;
    var x0 = hi0 * 967296;
    var x1 = (lo0 + x0) % 1000000;
    var x2 = hi0*4294+Math.floor((x0+lo0-x1)/1000000);
    return '' + x2 + h$jsstringDecIPadded6(x1);
}
function h$jsstringHexInteger(val) {
  ;
  if(((val).f === h$integerzmgmpZCGHCziIntegerziTypeziSzh_con_e)) {
    return '' + ((val).d1);
  } else {
    // we assume it's nonnegative. this condition is checked by the Haskell code
    return h$ghcjsbn_showBase(((val).d1), 16);
  }
}
function h$jsstringHexI64(hi,lo) {
    var lo0 = lo<0 ? lo+4294967296 : lo;
    if(hi === 0) return lo0.toString(16);
    return ((hi<0)?hi+4294967296:hi).toString(16) + h$jsstringHexIPadded8(lo0);
}
function h$jsstringHexW64(hi,lo) {
    var lo0 = lo<0 ? lo+4294967296 : lo;
    if(hi === 0) return lo0.toString(16);
    return ((hi<0)?hi+4294967296:hi).toString(16) + h$jsstringHexIPadded8(lo0);
}
// n in [0, 1000000000)
function h$jsstringDecIPadded9(n) {
    ;
    if(n === 0) return '000000000';
    var pad = (n>=100000000)?'':
              (n>=10000000)?'0':
              (n>=1000000)?'00':
              (n>=100000)?'000':
              (n>=10000)?'0000':
              (n>=1000)?'00000':
              (n>=100)?'000000':
              (n>=10)?'0000000':
                     '00000000';
    return pad+n;
}
// n in [0, 1000000)
function h$jsstringDecIPadded6(n) {
    ;
    if(n === 0) return '000000';
    var pad = (n>=100000)?'':
              (n>=10000)?'0':
              (n>=1000)?'00':
              (n>=100)?'000':
              (n>=10)?'0000':
                     '00000';
    return pad+n;
}
// n in [0, 2147483648)
function h$jsstringHexIPadded8(n) {
    ;
   if(n === 0) return '00000000';
   var pad = (n>=0x10000000)?'':
             (n>=0x1000000)?'0':
             (n>=0x100000)?'00':
             (n>=0x10000)?'000':
             (n>=0x1000)?'0000':
             (n>=0x100)?'00000':
             (n>=0x10)?'000000':
                      '0000000';
    return pad+n.toString(16);
}
function h$jsstringZeroes(n) {
    var r;
    switch(n&7) {
 case 0: r = ''; break;
 case 1: r = '0'; break;
 case 2: r = '00'; break;
 case 3: r = '000'; break;
 case 4: r = '0000'; break;
 case 5: r = '00000'; break;
 case 6: r = '000000'; break;
 case 7: r = '0000000';
    }
    for(var i=n>>3;i>0;i--) r = r + '00000000';
    return r;
}
function h$jsstringDoubleToFixed(decs, d) {
    if(decs >= 0) {
 if(Math.abs(d) < 1e21) {
     var r = d.toFixed(Math.min(20,decs));
     if(decs > 20) r = r + h$jsstringZeroes(decs-20);
     return r;
 } else {
     var r = d.toExponential();
     var ei = r.indexOf('e');
     var di = r.indexOf('.');
     var e = parseInt(r.substr(ei+1));
     return r.substring(0,di) + r.substring(di,ei) + h$jsstringZeroes(di-ei+e) +
                   ((decs > 0) ? ('.' + h$jsstringZeroes(decs)) : '');
 }
    }
    var r = Math.abs(d).toExponential();
    var ei = r.indexOf('e');
    var e = parseInt(r.substr(ei+1));
    var m = d < 0 ? '-' : '';
    r = r.substr(0,1) + r.substring(2,ei);
    if(e >= 0) {
 return (e > r.length) ? m + r + h$jsstringZeroes(r.length-e-1) + '.0'
                       : m + r.substr(0,e+1) + '.' + r.substr(e+1);
    } else {
 return m + '0.' + h$jsstringZeroes(-e-1) + r;
    }
}
function h$jsstringDoubleToExponent(decs, d) {
    var r;
    if(decs ===-1) {
 r = d.toExponential().replace('+','');
    } else {
 r = d.toExponential(Math.max(1, Math.min(20,decs))).replace('+','');
    }
    if(r.indexOf('.') === -1) {
 r = r.replace('e', '.0e');
    }
    if(decs > 20) r = r.replace('e', h$jsstringZeroes(decs-20)+'e');
    return r;
}
function h$jsstringDoubleGeneric(decs, d) {
    var r;
    if(decs === -1) {
 r = d.toString(10).replace('+','');
    } else {
 r = d.toPrecision(Math.max(decs+1,1)).replace('+','');
    }
    if(decs !== 0 && r.indexOf('.') === -1) {
 if(r.indexOf('e') !== -1) {
     r = r.replace('e', '.0e');
 } else {
     r = r + '.0';
 }
    }
    return r;
}
function h$jsstringAppend(x, y) {
    ;
    return x+y;
}
function h$jsstringCompare(x, y) {
    ;
    return (x<y)?-1:((x>y)?1:0);
}
function h$jsstringUnlines(xs) {
    var r = '';
    while(((xs).f === h$ghczmprimZCGHCziTypesziZC_con_e)) {
 r = r + ((((xs).d1)).d1) + '\n';
 xs = ((xs).d2);
    }
    return r;
}
function h$jsstringUnwords(xs) {
    if(((xs).f === h$ghczmprimZCGHCziTypesziZMZN_con_e)) return '';
    var r = ((((xs).d1)).d1);
    xs = ((xs).d2);
    while(((xs).f === h$ghczmprimZCGHCziTypesziZC_con_e)) {
 r = r + ' ' + ((((xs).d1)).d1);
 xs = ((xs).d2);
    }
    return r;
}
function h$jsstringReplace(pat, rep, src) {
    ;
    var r = src.replace(pat, rep, 'g');
    // the 'g' flag is not supported everywhere, check and fall back if necessary
    if(r.indexOf(pat) !== -1) {
 r = src.split(pat).join(rep);
    }
    return r;
}
function h$jsstringReplicateChar(n, ch) {
    ;
    return h$jsstringReplicate(n, h$jsstringSingleton(ch));
}
function h$jsstringIsInteger(str) {
    return /^-?\d+$/.test(str);
}
function h$jsstringIsNatural(str) {
    return /^\d+$/.test(str);
}
function h$jsstringReadInt(str) {
    if(!/^-?\d+/.test(str)) return null;
    var x = parseInt(str, 10);
    var x0 = x|0;
    return (x===x0) ? x0 : null;
}
function h$jsstringLenientReadInt(str) {
    var x = parseInt(str, 10);
    var x0 = x|0;
    return (x===x0) ? x0 : null;
}
function h$jsstringReadWord(str) {
  if(!/^\d+/.test(str)) return null;
  var x = parseInt(str, 10);
  var x0 = x|0;
  if(x0<0) return (x===x0+2147483648) ? x0 : null;
  else return (x===x0) ? x0 : null;
}
function h$jsstringReadDouble(str) {
    return parseFloat(str, 10);
}
function h$jsstringLenientReadDouble(str) {
    return parseFloat(str, 10);
}
function h$jsstringReadInteger(str) {
  ;
  if(!/^(-)?\d+$/.test(str)) {
    return null;
  } else if(str.length <= 9) {
    return (h$c1(h$integerzmgmpZCGHCziIntegerziTypeziSzh_con_e, (parseInt(str, 10))));;
  } else {
    return h$ghcjsbn_readInteger(str);
  }
}
function h$jsstringReadInt64(str) {
  if(!/^(-)?\d+$/.test(str)) {
      { h$ret1 = (0); h$ret2 = (0); return (0); };
  }
  if(str.charCodeAt(0) === 45) { // '-'
    return h$jsstringReadValue64(str, 1, true);
  } else {
    return h$jsstringReadValue64(str, 0, false);
  }
}
function h$jsstringReadWord64(str) {
  if(!/^\d+$/.test(str)) {
    { h$ret1 = (0); h$ret2 = (0); return (0); };
  }
  return h$jsstringReadValue64(str, 0, false);
}
var h$jsstringLongs = null;
function h$jsstringReadValue64(str, start, negate) {
  var l = str.length, i = start;
  while(i < l) {
    if(str.charCodeAt(i) !== 48) break;
    i++;
  }
  if(i >= l) { h$ret1 = (0); h$ret2 = (0); return (1); }; // only zeroes
  if(h$jsstringLongs === null) {
    h$jsstringLongs = [];
    for(var t=10; t<=1000000000; t*=10) {
      h$jsstringLongs.push(goog.math.Long.fromInt(t));
    }
  }
  var li = l-i;
  if(li < 10 && !negate) {
    { h$ret1 = (0); h$ret2 = (parseInt(str.substr(i), 10)); return (1); };
  }
  var r = goog.math.Long.fromInt(parseInt(str.substr(li,9),10));
  li += 9;
  while(li < l) {
    r = r.multiply(h$jsstringLongs[Math.min(l-li-1,8)])
         .add(goog.math.Long.fromInt(parseInt(str.substr(li,9), 10)));
    li += 9;
  }
  if(negate) {
    r = r.negate();
  }
  { h$ret1 = (r.getHighBits()); h$ret2 = (r.getLowBits()); return (1); };
}
function h$jsstringExecRE(i, str, re) {
    re.lastIndex = i;
    var m = re.exec(str);
    if(m === null) return -1;
    var a = [], x, j = 1, r = h$ghczmprimZCGHCziTypesziZMZN;
    while(true) {
 x = m[j];
 if(typeof x === 'undefined') break;
 a[j-1] = x;
 j++;
    }
    j-=1;
    while(--j>=0) r = (h$c2(h$ghczmprimZCGHCziTypesziZC_con_e, ((h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (a[j])))), (r)));
    { h$ret1 = (m[0]); h$ret2 = (r); return (m.index); };
}
function h$jsstringReplaceRE(pat, replacement, str) {
    return str.replace(pat, replacement);
}
function h$jsstringSplitRE(limit, re, str) {
    re.lastIndex = i;
    var s = (limit < 0) ? str.split(re) : str.split(re, limit);
    var i = s.length, r = h$ghczmprimZCGHCziTypesziZMZN;
    while(--i>=0) r = (h$c2(h$ghczmprimZCGHCziTypesziZC_con_e, ((h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (a[i])))), (r)));
    return r;
}
/* Copyright (C) 1991-2017 Free Software Foundation, Inc.
   This file is part of the GNU C Library.

   The GNU C Library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2.1 of the License, or (at your option) any later version.

   The GNU C Library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public
   License along with the GNU C Library; if not, see
   <http://www.gnu.org/licenses/>.  */
/* This header is separate from features.h so that the compiler can
   include it implicitly at the start of every compilation.  It must
   not itself include <features.h> or any other header that includes
   <features.h> because the implicit include comes before any feature
   test macros that may be defined in a source file before it first
   explicitly includes a system header.  GCC knows the name of this
   header in order to preinclude it.  */
/* glibc's intent is to support the IEC 559 math functionality, real
   and complex.  If the GCC (4.9 and later) predefined macros
   specifying compiler intent are available, use them to determine
   whether the overall intent is to support these features; otherwise,
   presume an older compiler has intent to support these features and
   define these macros by default.  */
/* wchar_t uses Unicode 8.0.0.  Version 8.0 of the Unicode Standard is
   synchronized with ISO/IEC 10646:2014, plus Amendment 1 (published
   2015-05-15).  */
/* We do not support C11 <threads.h>.  */
// values defined in Gen2.ClosureInfo
// thread status
/*
 * low-level heap object manipulation macros
 */
// GHCJS.Prim.JSVal
// GHCJS.Prim.JSException
// Exception dictionary for JSException
// SomeException
// GHC.Ptr.Ptr
// GHC.Integer.GMP.Internals
// Data.Maybe.Maybe
// #define HS_NOTHING h$nothing
// Data.List
// Data.Text
// Data.Text.Lazy
// black holes
// can we skip the indirection for black holes?
// resumable thunks
// general deconstruction
// retrieve  a numeric value that's possibly stored as an indirection
// generic lazy values
// generic data constructors and selectors
// unboxed tuple returns
// #define RETURN_UBX_TUP1(x) return x;
/*
 * Functions that directly access JavaScript strings, ignoring character
 * widths and surrogate pairs.
 */
function h$jsstringRawChunksOf(k, x) {
    var l = x.length;
    if(l === 0) return h$ghczmprimZCGHCziTypesziZMZN;
    if(l <= k) return (h$c2(h$ghczmprimZCGHCziTypesziZC_con_e, ((h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (x)))), (h$ghczmprimZCGHCziTypesziZMZN)));
    var r=h$ghczmprimZCGHCziTypesziZMZN;
    for(var i=ls-k;i>=0;i-=k) r = (h$c2(h$ghczmprimZCGHCziTypesziZC_con_e, ((h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (x.substr(i,i+k))))), (r)));
    return r;
}
function h$jsstringRawSplitAt(k, x) {
    if(k === 0) return (h$c2(h$ghczmprimZCGHCziTupleziZLz2cUZR_con_e,(h$jsstringEmpty),((h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (x))))));
    if(k >= x.length) return (h$c2(h$ghczmprimZCGHCziTupleziZLz2cUZR_con_e,((h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (x)))),(h$jsstringEmpty)));
    return (h$c2(h$ghczmprimZCGHCziTupleziZLz2cUZR_con_e,((h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (x.substr(0,k))))),((h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (x.substr(k)))))));
}
/* Copyright (C) 1991-2017 Free Software Foundation, Inc.
   This file is part of the GNU C Library.

   The GNU C Library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2.1 of the License, or (at your option) any later version.

   The GNU C Library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public
   License along with the GNU C Library; if not, see
   <http://www.gnu.org/licenses/>.  */
/* This header is separate from features.h so that the compiler can
   include it implicitly at the start of every compilation.  It must
   not itself include <features.h> or any other header that includes
   <features.h> because the implicit include comes before any feature
   test macros that may be defined in a source file before it first
   explicitly includes a system header.  GCC knows the name of this
   header in order to preinclude it.  */
/* glibc's intent is to support the IEC 559 math functionality, real
   and complex.  If the GCC (4.9 and later) predefined macros
   specifying compiler intent are available, use them to determine
   whether the overall intent is to support these features; otherwise,
   presume an older compiler has intent to support these features and
   define these macros by default.  */
/* wchar_t uses Unicode 8.0.0.  Version 8.0 of the Unicode Standard is
   synchronized with ISO/IEC 10646:2014, plus Amendment 1 (published
   2015-05-15).  */
/* We do not support C11 <threads.h>.  */
function h$foreignListProps(o) {
    var r = HS_NIL;
    if(typeof o === 'undefined' || o === null) return null;
    throw "h$foreignListProps";
/*    for(var p in o) {

    } */
}
/* Copyright (C) 1991-2017 Free Software Foundation, Inc.
   This file is part of the GNU C Library.

   The GNU C Library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2.1 of the License, or (at your option) any later version.

   The GNU C Library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public
   License along with the GNU C Library; if not, see
   <http://www.gnu.org/licenses/>.  */
/* This header is separate from features.h so that the compiler can
   include it implicitly at the start of every compilation.  It must
   not itself include <features.h> or any other header that includes
   <features.h> because the implicit include comes before any feature
   test macros that may be defined in a source file before it first
   explicitly includes a system header.  GCC knows the name of this
   header in order to preinclude it.  */
/* glibc's intent is to support the IEC 559 math functionality, real
   and complex.  If the GCC (4.9 and later) predefined macros
   specifying compiler intent are available, use them to determine
   whether the overall intent is to support these features; otherwise,
   presume an older compiler has intent to support these features and
   define these macros by default.  */
/* wchar_t uses Unicode 8.0.0.  Version 8.0 of the Unicode Standard is
   synchronized with ISO/IEC 10646:2014, plus Amendment 1 (published
   2015-05-15).  */
/* We do not support C11 <threads.h>.  */
// conversion between JavaScript string and Data.Text
// values defined in Gen2.ClosureInfo
// thread status
/*
 * low-level heap object manipulation macros
 */
// GHCJS.Prim.JSVal
// GHCJS.Prim.JSException
// Exception dictionary for JSException
// SomeException
// GHC.Ptr.Ptr
// GHC.Integer.GMP.Internals
// Data.Maybe.Maybe
// #define HS_NOTHING h$nothing
// Data.List
// Data.Text
// Data.Text.Lazy
// black holes
// can we skip the indirection for black holes?
// resumable thunks
// general deconstruction
// retrieve  a numeric value that's possibly stored as an indirection
// generic lazy values
// generic data constructors and selectors
// unboxed tuple returns
// #define RETURN_UBX_TUP1(x) return x;
/*
  convert a Data.Text buffer with offset/length to a JavaScript string
 */
function h$textToString(arr, off, len) {
    var a = [];
    var end = off+len;
    var k = 0;
    var u1 = arr.u1;
    var s = '';
    for(var i=off;i<end;i++) {
 var cc = u1[i];
 a[k++] = cc;
 if(k === 60000) {
     s += String.fromCharCode.apply(this, a);
     k = 0;
     a = [];
 }
    }
    return s + String.fromCharCode.apply(this, a);
}
/*
   convert a JavaScript string to a Data.Text buffer, second return
   value is length
 */
function h$textFromString(s) {
    var l = s.length;
    var b = h$newByteArray(l * 2);
    var u1 = b.u1;
    for(var i=l-1;i>=0;i--) u1[i] = s.charCodeAt(i);
    { h$ret1 = (l); return (b); };
}
function h$lazyTextToString(txt) {
    var s = '';
    while(((txt).f.a === 2)) {
        var head = ((txt));
        s += h$textToString(((head).d1), ((head).d2.d1), ((head).d2.d2));
        txt = ((txt).d2.d3);
    }
    return s;
}
function h$safeTextFromString(x) {
    if(typeof x !== 'string') {
 { h$ret1 = (0); return (null); };
    }
    return h$textFromString(x);
}
/* Copyright (C) 1991-2017 Free Software Foundation, Inc.
   This file is part of the GNU C Library.

   The GNU C Library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2.1 of the License, or (at your option) any later version.

   The GNU C Library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public
   License along with the GNU C Library; if not, see
   <http://www.gnu.org/licenses/>.  */
/* This header is separate from features.h so that the compiler can
   include it implicitly at the start of every compilation.  It must
   not itself include <features.h> or any other header that includes
   <features.h> because the implicit include comes before any feature
   test macros that may be defined in a source file before it first
   explicitly includes a system header.  GCC knows the name of this
   header in order to preinclude it.  */
/* glibc's intent is to support the IEC 559 math functionality, real
   and complex.  If the GCC (4.9 and later) predefined macros
   specifying compiler intent are available, use them to determine
   whether the overall intent is to support these features; otherwise,
   presume an older compiler has intent to support these features and
   define these macros by default.  */
/* wchar_t uses Unicode 8.0.0.  Version 8.0 of the Unicode Standard is
   synchronized with ISO/IEC 10646:2014, plus Amendment 1 (published
   2015-05-15).  */
/* We do not support C11 <threads.h>.  */
// values defined in Gen2.ClosureInfo
// thread status
/*
 * low-level heap object manipulation macros
 */
// GHCJS.Prim.JSVal
// GHCJS.Prim.JSException
// Exception dictionary for JSException
// SomeException
// GHC.Ptr.Ptr
// GHC.Integer.GMP.Internals
// Data.Maybe.Maybe
// #define HS_NOTHING h$nothing
// Data.List
// Data.Text
// Data.Text.Lazy
// black holes
// can we skip the indirection for black holes?
// resumable thunks
// general deconstruction
// retrieve  a numeric value that's possibly stored as an indirection
// generic lazy values
// generic data constructors and selectors
// unboxed tuple returns
// #define RETURN_UBX_TUP1(x) return x;
function h$allProps(o) {
    var a = [], i = 0;
    for(var p in o) a[i++] = p;
    return a;
}
function h$listAllProps(o) {
    var r = h$ghczmprimZCGHCziTypesziZMZN;
    for(var p in o) { r = (h$c2(h$ghczmprimZCGHCziTypesziZC_con_e, ((h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (p)))), (r))); }
    return r;
}
function h$listAssocs(o) {
    var r = h$ghczmprimZCGHCziTypesziZMZN;
    for(var p in o) { r = (h$c2(h$ghczmprimZCGHCziTypesziZC_con_e, ((h$c2(h$ghczmprimZCGHCziTupleziZLz2cUZR_con_e,((h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (p)))),((h$c1(h$ghcjszmprimZCGHCJSziPrimziJSVal_con_e, (o[p]))))))), (r))); }
    return r;
}
function h$isNumber(o) {
    return typeof(o) === 'number';
}
// returns true for null, but not for functions and host objects
function h$isObject(o) {
    return typeof(o) === 'object';
}
function h$isString(o) {
    return typeof(o) === 'string';
}
function h$isSymbol(o) {
    return typeof(o) === 'symbol';
}
function h$isBoolean(o) {
    return typeof(o) === 'boolean';
}
function h$isFunction(o) {
    return typeof(o) === 'function';
}
function h$jsTypeOf(o) {
    var t = typeof(o);
    if(t === 'undefined') return 0;
    if(t === 'object') return 1;
    if(t === 'boolean') return 2;
    if(t === 'number') return 3;
    if(t === 'string') return 4;
    if(t === 'symbol') return 5;
    if(t === 'function') return 6;
    return 7; // other, host object etc
}
/*
        -- 0 - null, 1 - integer,
        -- 2 - float, 3 - bool,
        -- 4 - string, 5 - array
        -- 6 - object
*/
function h$jsonTypeOf(o) {
    if (!(o instanceof Object)) {
        if (o == null) {
            return 0;
        } else if (typeof o == 'number') {
            if (h$isInteger(o)) {
                return 1;
            } else {
                return 2;
            }
        } else if (typeof o == 'boolean') {
            return 3;
        } else {
            return 4;
        }
    } else {
        if (Object.prototype.toString.call(o) == '[object Array]') {
            // it's an array
            return 5;
        } else if (!o) {
            // null 
            return 0;
        } else {
            // it's an object
            return 6;
        }
    }
}
/* Copyright (C) 1991-2017 Free Software Foundation, Inc.
   This file is part of the GNU C Library.

   The GNU C Library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2.1 of the License, or (at your option) any later version.

   The GNU C Library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public
   License along with the GNU C Library; if not, see
   <http://www.gnu.org/licenses/>.  */
/* This header is separate from features.h so that the compiler can
   include it implicitly at the start of every compilation.  It must
   not itself include <features.h> or any other header that includes
   <features.h> because the implicit include comes before any feature
   test macros that may be defined in a source file before it first
   explicitly includes a system header.  GCC knows the name of this
   header in order to preinclude it.  */
/* glibc's intent is to support the IEC 559 math functionality, real
   and complex.  If the GCC (4.9 and later) predefined macros
   specifying compiler intent are available, use them to determine
   whether the overall intent is to support these features; otherwise,
   presume an older compiler has intent to support these features and
   define these macros by default.  */
/* wchar_t uses Unicode 8.0.0.  Version 8.0 of the Unicode Standard is
   synchronized with ISO/IEC 10646:2014, plus Amendment 1 (published
   2015-05-15).  */
/* We do not support C11 <threads.h>.  */
function h$sendXHR(xhr, d, cont) {
    xhr.addEventListener('error', function () {
 cont(2);
    });
    xhr.addEventListener('abort', function() {
 cont(1);
    });
    xhr.addEventListener('load', function() {
 cont(0);
    });
    if(d) {
 xhr.send(d);
    } else {
 xhr.send();
    }
}
/* Copyright (C) 1991-2017 Free Software Foundation, Inc.
   This file is part of the GNU C Library.

   The GNU C Library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2.1 of the License, or (at your option) any later version.

   The GNU C Library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public
   License along with the GNU C Library; if not, see
   <http://www.gnu.org/licenses/>.  */
/* This header is separate from features.h so that the compiler can
   include it implicitly at the start of every compilation.  It must
   not itself include <features.h> or any other header that includes
   <features.h> because the implicit include comes before any feature
   test macros that may be defined in a source file before it first
   explicitly includes a system header.  GCC knows the name of this
   header in order to preinclude it.  */
/* glibc's intent is to support the IEC 559 math functionality, real
   and complex.  If the GCC (4.9 and later) predefined macros
   specifying compiler intent are available, use them to determine
   whether the overall intent is to support these features; otherwise,
   presume an older compiler has intent to support these features and
   define these macros by default.  */
/* wchar_t uses Unicode 8.0.0.  Version 8.0 of the Unicode Standard is
   synchronized with ISO/IEC 10646:2014, plus Amendment 1 (published
   2015-05-15).  */
/* We do not support C11 <threads.h>.  */
/*! jQuery v2.1.4 | (c) 2005, 2015 jQuery Foundation, Inc. | jquery.org/license */
!function(a,b){"object"==typeof module&&"object"==typeof module.exports?module.exports=a.document?b(a,!0):function(a){if(!a.document)throw new Error("jQuery requires a window with a document");return b(a)}:b(a)}("undefined"!=typeof window?window:this,function(a,b){var c=[],d=c.slice,e=c.concat,f=c.push,g=c.indexOf,h={},i=h.toString,j=h.hasOwnProperty,k={},l=a.document,m="2.1.4",n=function(a,b){return new n.fn.init(a,b)},o=/^[\s\uFEFF\xA0]+|[\s\uFEFF\xA0]+$/g,p=/^-ms-/,q=/-([\da-z])/gi,r=function(a,b){return b.toUpperCase()};n.fn=n.prototype={jquery:m,constructor:n,selector:"",length:0,toArray:function(){return d.call(this)},get:function(a){return null!=a?0>a?this[a+this.length]:this[a]:d.call(this)},pushStack:function(a){var b=n.merge(this.constructor(),a);return b.prevObject=this,b.context=this.context,b},each:function(a,b){return n.each(this,a,b)},map:function(a){return this.pushStack(n.map(this,function(b,c){return a.call(b,c,b)}))},slice:function(){return this.pushStack(d.apply(this,arguments))},first:function(){return this.eq(0)},last:function(){return this.eq(-1)},eq:function(a){var b=this.length,c=+a+(0>a?b:0);return this.pushStack(c>=0&&b>c?[this[c]]:[])},end:function(){return this.prevObject||this.constructor(null)},push:f,sort:c.sort,splice:c.splice},n.extend=n.fn.extend=function(){var a,b,c,d,e,f,g=arguments[0]||{},h=1,i=arguments.length,j=!1;for("boolean"==typeof g&&(j=g,g=arguments[h]||{},h++),"object"==typeof g||n.isFunction(g)||(g={}),h===i&&(g=this,h--);i>h;h++)if(null!=(a=arguments[h]))for(b in a)c=g[b],d=a[b],g!==d&&(j&&d&&(n.isPlainObject(d)||(e=n.isArray(d)))?(e?(e=!1,f=c&&n.isArray(c)?c:[]):f=c&&n.isPlainObject(c)?c:{},g[b]=n.extend(j,f,d)):void 0!==d&&(g[b]=d));return g},n.extend({expando:"jQuery"+(m+Math.random()).replace(/\D/g,""),isReady:!0,error:function(a){throw new Error(a)},noop:function(){},isFunction:function(a){return"function"===n.type(a)},isArray:Array.isArray,isWindow:function(a){return null!=a&&a===a.window},isNumeric:function(a){return!n.isArray(a)&&a-parseFloat(a)+1>=0},isPlainObject:function(a){return"object"!==n.type(a)||a.nodeType||n.isWindow(a)?!1:a.constructor&&!j.call(a.constructor.prototype,"isPrototypeOf")?!1:!0},isEmptyObject:function(a){var b;for(b in a)return!1;return!0},type:function(a){return null==a?a+"":"object"==typeof a||"function"==typeof a?h[i.call(a)]||"object":typeof a},globalEval:function(a){var b,c=eval;a=n.trim(a),a&&(1===a.indexOf("use strict")?(b=l.createElement("script"),b.text=a,l.head.appendChild(b).parentNode.removeChild(b)):c(a))},camelCase:function(a){return a.replace(p,"ms-").replace(q,r)},nodeName:function(a,b){return a.nodeName&&a.nodeName.toLowerCase()===b.toLowerCase()},each:function(a,b,c){var d,e=0,f=a.length,g=s(a);if(c){if(g){for(;f>e;e++)if(d=b.apply(a[e],c),d===!1)break}else for(e in a)if(d=b.apply(a[e],c),d===!1)break}else if(g){for(;f>e;e++)if(d=b.call(a[e],e,a[e]),d===!1)break}else for(e in a)if(d=b.call(a[e],e,a[e]),d===!1)break;return a},trim:function(a){return null==a?"":(a+"").replace(o,"")},makeArray:function(a,b){var c=b||[];return null!=a&&(s(Object(a))?n.merge(c,"string"==typeof a?[a]:a):f.call(c,a)),c},inArray:function(a,b,c){return null==b?-1:g.call(b,a,c)},merge:function(a,b){for(var c=+b.length,d=0,e=a.length;c>d;d++)a[e++]=b[d];return a.length=e,a},grep:function(a,b,c){for(var d,e=[],f=0,g=a.length,h=!c;g>f;f++)d=!b(a[f],f),d!==h&&e.push(a[f]);return e},map:function(a,b,c){var d,f=0,g=a.length,h=s(a),i=[];if(h)for(;g>f;f++)d=b(a[f],f,c),null!=d&&i.push(d);else for(f in a)d=b(a[f],f,c),null!=d&&i.push(d);return e.apply([],i)},guid:1,proxy:function(a,b){var c,e,f;return"string"==typeof b&&(c=a[b],b=a,a=c),n.isFunction(a)?(e=d.call(arguments,2),f=function(){return a.apply(b||this,e.concat(d.call(arguments)))},f.guid=a.guid=a.guid||n.guid++,f):void 0},now:Date.now,support:k}),n.each("Boolean Number String Function Array Date RegExp Object Error".split(" "),function(a,b){h["[object "+b+"]"]=b.toLowerCase()});function s(a){var b="length"in a&&a.length,c=n.type(a);return"function"===c||n.isWindow(a)?!1:1===a.nodeType&&b?!0:"array"===c||0===b||"number"==typeof b&&b>0&&b-1 in a}var t=function(a){var b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u="sizzle"+1*new Date,v=a.document,w=0,x=0,y=ha(),z=ha(),A=ha(),B=function(a,b){return a===b&&(l=!0),0},C=1<<31,D={}.hasOwnProperty,E=[],F=E.pop,G=E.push,H=E.push,I=E.slice,J=function(a,b){for(var c=0,d=a.length;d>c;c++)if(a[c]===b)return c;return-1},K="checked|selected|async|autofocus|autoplay|controls|defer|disabled|hidden|ismap|loop|multiple|open|readonly|required|scoped",L="[\\x20\\t\\r\\n\\f]",M="(?:\\\\.|[\\w-]|[^\\x00-\\xa0])+",N=M.replace("w","w#"),O="\\["+L+"*("+M+")(?:"+L+"*([*^$|!~]?=)"+L+"*(?:'((?:\\\\.|[^\\\\'])*)'|\"((?:\\\\.|[^\\\\\"])*)\"|("+N+"))|)"+L+"*\\]",P=":("+M+")(?:\\((('((?:\\\\.|[^\\\\'])*)'|\"((?:\\\\.|[^\\\\\"])*)\")|((?:\\\\.|[^\\\\()[\\]]|"+O+")*)|.*)\\)|)",Q=new RegExp(L+"+","g"),R=new RegExp("^"+L+"+|((?:^|[^\\\\])(?:\\\\.)*)"+L+"+$","g"),S=new RegExp("^"+L+"*,"+L+"*"),T=new RegExp("^"+L+"*([>+~]|"+L+")"+L+"*"),U=new RegExp("="+L+"*([^\\]'\"]*?)"+L+"*\\]","g"),V=new RegExp(P),W=new RegExp("^"+N+"$"),X={ID:new RegExp("^#("+M+")"),CLASS:new RegExp("^\\.("+M+")"),TAG:new RegExp("^("+M.replace("w","w*")+")"),ATTR:new RegExp("^"+O),PSEUDO:new RegExp("^"+P),CHILD:new RegExp("^:(only|first|last|nth|nth-last)-(child|of-type)(?:\\("+L+"*(even|odd|(([+-]|)(\\d*)n|)"+L+"*(?:([+-]|)"+L+"*(\\d+)|))"+L+"*\\)|)","i"),bool:new RegExp("^(?:"+K+")$","i"),needsContext:new RegExp("^"+L+"*[>+~]|:(even|odd|eq|gt|lt|nth|first|last)(?:\\("+L+"*((?:-\\d)?\\d*)"+L+"*\\)|)(?=[^-]|$)","i")},Y=/^(?:input|select|textarea|button)$/i,Z=/^h\d$/i,$=/^[^{]+\{\s*\[native \w/,_=/^(?:#([\w-]+)|(\w+)|\.([\w-]+))$/,aa=/[+~]/,ba=/'|\\/g,ca=new RegExp("\\\\([\\da-f]{1,6}"+L+"?|("+L+")|.)","ig"),da=function(a,b,c){var d="0x"+b-65536;return d!==d||c?b:0>d?String.fromCharCode(d+65536):String.fromCharCode(d>>10|55296,1023&d|56320)},ea=function(){m()};try{H.apply(E=I.call(v.childNodes),v.childNodes),E[v.childNodes.length].nodeType}catch(fa){H={apply:E.length?function(a,b){G.apply(a,I.call(b))}:function(a,b){var c=a.length,d=0;while(a[c++]=b[d++]);a.length=c-1}}}function ga(a,b,d,e){var f,h,j,k,l,o,r,s,w,x;if((b?b.ownerDocument||b:v)!==n&&m(b),b=b||n,d=d||[],k=b.nodeType,"string"!=typeof a||!a||1!==k&&9!==k&&11!==k)return d;if(!e&&p){if(11!==k&&(f=_.exec(a)))if(j=f[1]){if(9===k){if(h=b.getElementById(j),!h||!h.parentNode)return d;if(h.id===j)return d.push(h),d}else if(b.ownerDocument&&(h=b.ownerDocument.getElementById(j))&&t(b,h)&&h.id===j)return d.push(h),d}else{if(f[2])return H.apply(d,b.getElementsByTagName(a)),d;if((j=f[3])&&c.getElementsByClassName)return H.apply(d,b.getElementsByClassName(j)),d}if(c.qsa&&(!q||!q.test(a))){if(s=r=u,w=b,x=1!==k&&a,1===k&&"object"!==b.nodeName.toLowerCase()){o=g(a),(r=b.getAttribute("id"))?s=r.replace(ba,"\\$&"):b.setAttribute("id",s),s="[id='"+s+"'] ",l=o.length;while(l--)o[l]=s+ra(o[l]);w=aa.test(a)&&pa(b.parentNode)||b,x=o.join(",")}if(x)try{return H.apply(d,w.querySelectorAll(x)),d}catch(y){}finally{r||b.removeAttribute("id")}}}return i(a.replace(R,"$1"),b,d,e)}function ha(){var a=[];function b(c,e){return a.push(c+" ")>d.cacheLength&&delete b[a.shift()],b[c+" "]=e}return b}function ia(a){return a[u]=!0,a}function ja(a){var b=n.createElement("div");try{return!!a(b)}catch(c){return!1}finally{b.parentNode&&b.parentNode.removeChild(b),b=null}}function ka(a,b){var c=a.split("|"),e=a.length;while(e--)d.attrHandle[c[e]]=b}function la(a,b){var c=b&&a,d=c&&1===a.nodeType&&1===b.nodeType&&(~b.sourceIndex||C)-(~a.sourceIndex||C);if(d)return d;if(c)while(c=c.nextSibling)if(c===b)return-1;return a?1:-1}function ma(a){return function(b){var c=b.nodeName.toLowerCase();return"input"===c&&b.type===a}}function na(a){return function(b){var c=b.nodeName.toLowerCase();return("input"===c||"button"===c)&&b.type===a}}function oa(a){return ia(function(b){return b=+b,ia(function(c,d){var e,f=a([],c.length,b),g=f.length;while(g--)c[e=f[g]]&&(c[e]=!(d[e]=c[e]))})})}function pa(a){return a&&"undefined"!=typeof a.getElementsByTagName&&a}c=ga.support={},f=ga.isXML=function(a){var b=a&&(a.ownerDocument||a).documentElement;return b?"HTML"!==b.nodeName:!1},m=ga.setDocument=function(a){var b,e,g=a?a.ownerDocument||a:v;return g!==n&&9===g.nodeType&&g.documentElement?(n=g,o=g.documentElement,e=g.defaultView,e&&e!==e.top&&(e.addEventListener?e.addEventListener("unload",ea,!1):e.attachEvent&&e.attachEvent("onunload",ea)),p=!f(g),c.attributes=ja(function(a){return a.className="i",!a.getAttribute("className")}),c.getElementsByTagName=ja(function(a){return a.appendChild(g.createComment("")),!a.getElementsByTagName("*").length}),c.getElementsByClassName=$.test(g.getElementsByClassName),c.getById=ja(function(a){return o.appendChild(a).id=u,!g.getElementsByName||!g.getElementsByName(u).length}),c.getById?(d.find.ID=function(a,b){if("undefined"!=typeof b.getElementById&&p){var c=b.getElementById(a);return c&&c.parentNode?[c]:[]}},d.filter.ID=function(a){var b=a.replace(ca,da);return function(a){return a.getAttribute("id")===b}}):(delete d.find.ID,d.filter.ID=function(a){var b=a.replace(ca,da);return function(a){var c="undefined"!=typeof a.getAttributeNode&&a.getAttributeNode("id");return c&&c.value===b}}),d.find.TAG=c.getElementsByTagName?function(a,b){return"undefined"!=typeof b.getElementsByTagName?b.getElementsByTagName(a):c.qsa?b.querySelectorAll(a):void 0}:function(a,b){var c,d=[],e=0,f=b.getElementsByTagName(a);if("*"===a){while(c=f[e++])1===c.nodeType&&d.push(c);return d}return f},d.find.CLASS=c.getElementsByClassName&&function(a,b){return p?b.getElementsByClassName(a):void 0},r=[],q=[],(c.qsa=$.test(g.querySelectorAll))&&(ja(function(a){o.appendChild(a).innerHTML="<a id='"+u+"'></a><select id='"+u+"-\f]' msallowcapture=''><option selected=''></option></select>",a.querySelectorAll("[msallowcapture^='']").length&&q.push("[*^$]="+L+"*(?:''|\"\")"),a.querySelectorAll("[selected]").length||q.push("\\["+L+"*(?:value|"+K+")"),a.querySelectorAll("[id~="+u+"-]").length||q.push("~="),a.querySelectorAll(":checked").length||q.push(":checked"),a.querySelectorAll("a#"+u+"+*").length||q.push(".#.+[+~]")}),ja(function(a){var b=g.createElement("input");b.setAttribute("type","hidden"),a.appendChild(b).setAttribute("name","D"),a.querySelectorAll("[name=d]").length&&q.push("name"+L+"*[*^$|!~]?="),a.querySelectorAll(":enabled").length||q.push(":enabled",":disabled"),a.querySelectorAll("*,:x"),q.push(",.*:")})),(c.matchesSelector=$.test(s=o.matches||o.webkitMatchesSelector||o.mozMatchesSelector||o.oMatchesSelector||o.msMatchesSelector))&&ja(function(a){c.disconnectedMatch=s.call(a,"div"),s.call(a,"[s!='']:x"),r.push("!=",P)}),q=q.length&&new RegExp(q.join("|")),r=r.length&&new RegExp(r.join("|")),b=$.test(o.compareDocumentPosition),t=b||$.test(o.contains)?function(a,b){var c=9===a.nodeType?a.documentElement:a,d=b&&b.parentNode;return a===d||!(!d||1!==d.nodeType||!(c.contains?c.contains(d):a.compareDocumentPosition&&16&a.compareDocumentPosition(d)))}:function(a,b){if(b)while(b=b.parentNode)if(b===a)return!0;return!1},B=b?function(a,b){if(a===b)return l=!0,0;var d=!a.compareDocumentPosition-!b.compareDocumentPosition;return d?d:(d=(a.ownerDocument||a)===(b.ownerDocument||b)?a.compareDocumentPosition(b):1,1&d||!c.sortDetached&&b.compareDocumentPosition(a)===d?a===g||a.ownerDocument===v&&t(v,a)?-1:b===g||b.ownerDocument===v&&t(v,b)?1:k?J(k,a)-J(k,b):0:4&d?-1:1)}:function(a,b){if(a===b)return l=!0,0;var c,d=0,e=a.parentNode,f=b.parentNode,h=[a],i=[b];if(!e||!f)return a===g?-1:b===g?1:e?-1:f?1:k?J(k,a)-J(k,b):0;if(e===f)return la(a,b);c=a;while(c=c.parentNode)h.unshift(c);c=b;while(c=c.parentNode)i.unshift(c);while(h[d]===i[d])d++;return d?la(h[d],i[d]):h[d]===v?-1:i[d]===v?1:0},g):n},ga.matches=function(a,b){return ga(a,null,null,b)},ga.matchesSelector=function(a,b){if((a.ownerDocument||a)!==n&&m(a),b=b.replace(U,"='$1']"),!(!c.matchesSelector||!p||r&&r.test(b)||q&&q.test(b)))try{var d=s.call(a,b);if(d||c.disconnectedMatch||a.document&&11!==a.document.nodeType)return d}catch(e){}return ga(b,n,null,[a]).length>0},ga.contains=function(a,b){return(a.ownerDocument||a)!==n&&m(a),t(a,b)},ga.attr=function(a,b){(a.ownerDocument||a)!==n&&m(a);var e=d.attrHandle[b.toLowerCase()],f=e&&D.call(d.attrHandle,b.toLowerCase())?e(a,b,!p):void 0;return void 0!==f?f:c.attributes||!p?a.getAttribute(b):(f=a.getAttributeNode(b))&&f.specified?f.value:null},ga.error=function(a){throw new Error("Syntax error, unrecognized expression: "+a)},ga.uniqueSort=function(a){var b,d=[],e=0,f=0;if(l=!c.detectDuplicates,k=!c.sortStable&&a.slice(0),a.sort(B),l){while(b=a[f++])b===a[f]&&(e=d.push(f));while(e--)a.splice(d[e],1)}return k=null,a},e=ga.getText=function(a){var b,c="",d=0,f=a.nodeType;if(f){if(1===f||9===f||11===f){if("string"==typeof a.textContent)return a.textContent;for(a=a.firstChild;a;a=a.nextSibling)c+=e(a)}else if(3===f||4===f)return a.nodeValue}else while(b=a[d++])c+=e(b);return c},d=ga.selectors={cacheLength:50,createPseudo:ia,match:X,attrHandle:{},find:{},relative:{">":{dir:"parentNode",first:!0}," ":{dir:"parentNode"},"+":{dir:"previousSibling",first:!0},"~":{dir:"previousSibling"}},preFilter:{ATTR:function(a){return a[1]=a[1].replace(ca,da),a[3]=(a[3]||a[4]||a[5]||"").replace(ca,da),"~="===a[2]&&(a[3]=" "+a[3]+" "),a.slice(0,4)},CHILD:function(a){return a[1]=a[1].toLowerCase(),"nth"===a[1].slice(0,3)?(a[3]||ga.error(a[0]),a[4]=+(a[4]?a[5]+(a[6]||1):2*("even"===a[3]||"odd"===a[3])),a[5]=+(a[7]+a[8]||"odd"===a[3])):a[3]&&ga.error(a[0]),a},PSEUDO:function(a){var b,c=!a[6]&&a[2];return X.CHILD.test(a[0])?null:(a[3]?a[2]=a[4]||a[5]||"":c&&V.test(c)&&(b=g(c,!0))&&(b=c.indexOf(")",c.length-b)-c.length)&&(a[0]=a[0].slice(0,b),a[2]=c.slice(0,b)),a.slice(0,3))}},filter:{TAG:function(a){var b=a.replace(ca,da).toLowerCase();return"*"===a?function(){return!0}:function(a){return a.nodeName&&a.nodeName.toLowerCase()===b}},CLASS:function(a){var b=y[a+" "];return b||(b=new RegExp("(^|"+L+")"+a+"("+L+"|$)"))&&y(a,function(a){return b.test("string"==typeof a.className&&a.className||"undefined"!=typeof a.getAttribute&&a.getAttribute("class")||"")})},ATTR:function(a,b,c){return function(d){var e=ga.attr(d,a);return null==e?"!="===b:b?(e+="","="===b?e===c:"!="===b?e!==c:"^="===b?c&&0===e.indexOf(c):"*="===b?c&&e.indexOf(c)>-1:"$="===b?c&&e.slice(-c.length)===c:"~="===b?(" "+e.replace(Q," ")+" ").indexOf(c)>-1:"|="===b?e===c||e.slice(0,c.length+1)===c+"-":!1):!0}},CHILD:function(a,b,c,d,e){var f="nth"!==a.slice(0,3),g="last"!==a.slice(-4),h="of-type"===b;return 1===d&&0===e?function(a){return!!a.parentNode}:function(b,c,i){var j,k,l,m,n,o,p=f!==g?"nextSibling":"previousSibling",q=b.parentNode,r=h&&b.nodeName.toLowerCase(),s=!i&&!h;if(q){if(f){while(p){l=b;while(l=l[p])if(h?l.nodeName.toLowerCase()===r:1===l.nodeType)return!1;o=p="only"===a&&!o&&"nextSibling"}return!0}if(o=[g?q.firstChild:q.lastChild],g&&s){k=q[u]||(q[u]={}),j=k[a]||[],n=j[0]===w&&j[1],m=j[0]===w&&j[2],l=n&&q.childNodes[n];while(l=++n&&l&&l[p]||(m=n=0)||o.pop())if(1===l.nodeType&&++m&&l===b){k[a]=[w,n,m];break}}else if(s&&(j=(b[u]||(b[u]={}))[a])&&j[0]===w)m=j[1];else while(l=++n&&l&&l[p]||(m=n=0)||o.pop())if((h?l.nodeName.toLowerCase()===r:1===l.nodeType)&&++m&&(s&&((l[u]||(l[u]={}))[a]=[w,m]),l===b))break;return m-=e,m===d||m%d===0&&m/d>=0}}},PSEUDO:function(a,b){var c,e=d.pseudos[a]||d.setFilters[a.toLowerCase()]||ga.error("unsupported pseudo: "+a);return e[u]?e(b):e.length>1?(c=[a,a,"",b],d.setFilters.hasOwnProperty(a.toLowerCase())?ia(function(a,c){var d,f=e(a,b),g=f.length;while(g--)d=J(a,f[g]),a[d]=!(c[d]=f[g])}):function(a){return e(a,0,c)}):e}},pseudos:{not:ia(function(a){var b=[],c=[],d=h(a.replace(R,"$1"));return d[u]?ia(function(a,b,c,e){var f,g=d(a,null,e,[]),h=a.length;while(h--)(f=g[h])&&(a[h]=!(b[h]=f))}):function(a,e,f){return b[0]=a,d(b,null,f,c),b[0]=null,!c.pop()}}),has:ia(function(a){return function(b){return ga(a,b).length>0}}),contains:ia(function(a){return a=a.replace(ca,da),function(b){return(b.textContent||b.innerText||e(b)).indexOf(a)>-1}}),lang:ia(function(a){return W.test(a||"")||ga.error("unsupported lang: "+a),a=a.replace(ca,da).toLowerCase(),function(b){var c;do if(c=p?b.lang:b.getAttribute("xml:lang")||b.getAttribute("lang"))return c=c.toLowerCase(),c===a||0===c.indexOf(a+"-");while((b=b.parentNode)&&1===b.nodeType);return!1}}),target:function(b){var c=a.location&&a.location.hash;return c&&c.slice(1)===b.id},root:function(a){return a===o},focus:function(a){return a===n.activeElement&&(!n.hasFocus||n.hasFocus())&&!!(a.type||a.href||~a.tabIndex)},enabled:function(a){return a.disabled===!1},disabled:function(a){return a.disabled===!0},checked:function(a){var b=a.nodeName.toLowerCase();return"input"===b&&!!a.checked||"option"===b&&!!a.selected},selected:function(a){return a.parentNode&&a.parentNode.selectedIndex,a.selected===!0},empty:function(a){for(a=a.firstChild;a;a=a.nextSibling)if(a.nodeType<6)return!1;return!0},parent:function(a){return!d.pseudos.empty(a)},header:function(a){return Z.test(a.nodeName)},input:function(a){return Y.test(a.nodeName)},button:function(a){var b=a.nodeName.toLowerCase();return"input"===b&&"button"===a.type||"button"===b},text:function(a){var b;return"input"===a.nodeName.toLowerCase()&&"text"===a.type&&(null==(b=a.getAttribute("type"))||"text"===b.toLowerCase())},first:oa(function(){return[0]}),last:oa(function(a,b){return[b-1]}),eq:oa(function(a,b,c){return[0>c?c+b:c]}),even:oa(function(a,b){for(var c=0;b>c;c+=2)a.push(c);return a}),odd:oa(function(a,b){for(var c=1;b>c;c+=2)a.push(c);return a}),lt:oa(function(a,b,c){for(var d=0>c?c+b:c;--d>=0;)a.push(d);return a}),gt:oa(function(a,b,c){for(var d=0>c?c+b:c;++d<b;)a.push(d);return a})}},d.pseudos.nth=d.pseudos.eq;for(b in{radio:!0,checkbox:!0,file:!0,password:!0,image:!0})d.pseudos[b]=ma(b);for(b in{submit:!0,reset:!0})d.pseudos[b]=na(b);function qa(){}qa.prototype=d.filters=d.pseudos,d.setFilters=new qa,g=ga.tokenize=function(a,b){var c,e,f,g,h,i,j,k=z[a+" "];if(k)return b?0:k.slice(0);h=a,i=[],j=d.preFilter;while(h){(!c||(e=S.exec(h)))&&(e&&(h=h.slice(e[0].length)||h),i.push(f=[])),c=!1,(e=T.exec(h))&&(c=e.shift(),f.push({value:c,type:e[0].replace(R," ")}),h=h.slice(c.length));for(g in d.filter)!(e=X[g].exec(h))||j[g]&&!(e=j[g](e))||(c=e.shift(),f.push({value:c,type:g,matches:e}),h=h.slice(c.length));if(!c)break}return b?h.length:h?ga.error(a):z(a,i).slice(0)};function ra(a){for(var b=0,c=a.length,d="";c>b;b++)d+=a[b].value;return d}function sa(a,b,c){var d=b.dir,e=c&&"parentNode"===d,f=x++;return b.first?function(b,c,f){while(b=b[d])if(1===b.nodeType||e)return a(b,c,f)}:function(b,c,g){var h,i,j=[w,f];if(g){while(b=b[d])if((1===b.nodeType||e)&&a(b,c,g))return!0}else while(b=b[d])if(1===b.nodeType||e){if(i=b[u]||(b[u]={}),(h=i[d])&&h[0]===w&&h[1]===f)return j[2]=h[2];if(i[d]=j,j[2]=a(b,c,g))return!0}}}function ta(a){return a.length>1?function(b,c,d){var e=a.length;while(e--)if(!a[e](b,c,d))return!1;return!0}:a[0]}function ua(a,b,c){for(var d=0,e=b.length;e>d;d++)ga(a,b[d],c);return c}function va(a,b,c,d,e){for(var f,g=[],h=0,i=a.length,j=null!=b;i>h;h++)(f=a[h])&&(!c||c(f,d,e))&&(g.push(f),j&&b.push(h));return g}function wa(a,b,c,d,e,f){return d&&!d[u]&&(d=wa(d)),e&&!e[u]&&(e=wa(e,f)),ia(function(f,g,h,i){var j,k,l,m=[],n=[],o=g.length,p=f||ua(b||"*",h.nodeType?[h]:h,[]),q=!a||!f&&b?p:va(p,m,a,h,i),r=c?e||(f?a:o||d)?[]:g:q;if(c&&c(q,r,h,i),d){j=va(r,n),d(j,[],h,i),k=j.length;while(k--)(l=j[k])&&(r[n[k]]=!(q[n[k]]=l))}if(f){if(e||a){if(e){j=[],k=r.length;while(k--)(l=r[k])&&j.push(q[k]=l);e(null,r=[],j,i)}k=r.length;while(k--)(l=r[k])&&(j=e?J(f,l):m[k])>-1&&(f[j]=!(g[j]=l))}}else r=va(r===g?r.splice(o,r.length):r),e?e(null,g,r,i):H.apply(g,r)})}function xa(a){for(var b,c,e,f=a.length,g=d.relative[a[0].type],h=g||d.relative[" "],i=g?1:0,k=sa(function(a){return a===b},h,!0),l=sa(function(a){return J(b,a)>-1},h,!0),m=[function(a,c,d){var e=!g&&(d||c!==j)||((b=c).nodeType?k(a,c,d):l(a,c,d));return b=null,e}];f>i;i++)if(c=d.relative[a[i].type])m=[sa(ta(m),c)];else{if(c=d.filter[a[i].type].apply(null,a[i].matches),c[u]){for(e=++i;f>e;e++)if(d.relative[a[e].type])break;return wa(i>1&&ta(m),i>1&&ra(a.slice(0,i-1).concat({value:" "===a[i-2].type?"*":""})).replace(R,"$1"),c,e>i&&xa(a.slice(i,e)),f>e&&xa(a=a.slice(e)),f>e&&ra(a))}m.push(c)}return ta(m)}function ya(a,b){var c=b.length>0,e=a.length>0,f=function(f,g,h,i,k){var l,m,o,p=0,q="0",r=f&&[],s=[],t=j,u=f||e&&d.find.TAG("*",k),v=w+=null==t?1:Math.random()||.1,x=u.length;for(k&&(j=g!==n&&g);q!==x&&null!=(l=u[q]);q++){if(e&&l){m=0;while(o=a[m++])if(o(l,g,h)){i.push(l);break}k&&(w=v)}c&&((l=!o&&l)&&p--,f&&r.push(l))}if(p+=q,c&&q!==p){m=0;while(o=b[m++])o(r,s,g,h);if(f){if(p>0)while(q--)r[q]||s[q]||(s[q]=F.call(i));s=va(s)}H.apply(i,s),k&&!f&&s.length>0&&p+b.length>1&&ga.uniqueSort(i)}return k&&(w=v,j=t),r};return c?ia(f):f}return h=ga.compile=function(a,b){var c,d=[],e=[],f=A[a+" "];if(!f){b||(b=g(a)),c=b.length;while(c--)f=xa(b[c]),f[u]?d.push(f):e.push(f);f=A(a,ya(e,d)),f.selector=a}return f},i=ga.select=function(a,b,e,f){var i,j,k,l,m,n="function"==typeof a&&a,o=!f&&g(a=n.selector||a);if(e=e||[],1===o.length){if(j=o[0]=o[0].slice(0),j.length>2&&"ID"===(k=j[0]).type&&c.getById&&9===b.nodeType&&p&&d.relative[j[1].type]){if(b=(d.find.ID(k.matches[0].replace(ca,da),b)||[])[0],!b)return e;n&&(b=b.parentNode),a=a.slice(j.shift().value.length)}i=X.needsContext.test(a)?0:j.length;while(i--){if(k=j[i],d.relative[l=k.type])break;if((m=d.find[l])&&(f=m(k.matches[0].replace(ca,da),aa.test(j[0].type)&&pa(b.parentNode)||b))){if(j.splice(i,1),a=f.length&&ra(j),!a)return H.apply(e,f),e;break}}}return(n||h(a,o))(f,b,!p,e,aa.test(a)&&pa(b.parentNode)||b),e},c.sortStable=u.split("").sort(B).join("")===u,c.detectDuplicates=!!l,m(),c.sortDetached=ja(function(a){return 1&a.compareDocumentPosition(n.createElement("div"))}),ja(function(a){return a.innerHTML="<a href='#'></a>","#"===a.firstChild.getAttribute("href")})||ka("type|href|height|width",function(a,b,c){return c?void 0:a.getAttribute(b,"type"===b.toLowerCase()?1:2)}),c.attributes&&ja(function(a){return a.innerHTML="<input/>",a.firstChild.setAttribute("value",""),""===a.firstChild.getAttribute("value")})||ka("value",function(a,b,c){return c||"input"!==a.nodeName.toLowerCase()?void 0:a.defaultValue}),ja(function(a){return null==a.getAttribute("disabled")})||ka(K,function(a,b,c){var d;return c?void 0:a[b]===!0?b.toLowerCase():(d=a.getAttributeNode(b))&&d.specified?d.value:null}),ga}(a);n.find=t,n.expr=t.selectors,n.expr[":"]=n.expr.pseudos,n.unique=t.uniqueSort,n.text=t.getText,n.isXMLDoc=t.isXML,n.contains=t.contains;var u=n.expr.match.needsContext,v=/^<(\w+)\s*\/?>(?:<\/\1>|)$/,w=/^.[^:#\[\.,]*$/;function x(a,b,c){if(n.isFunction(b))return n.grep(a,function(a,d){return!!b.call(a,d,a)!==c});if(b.nodeType)return n.grep(a,function(a){return a===b!==c});if("string"==typeof b){if(w.test(b))return n.filter(b,a,c);b=n.filter(b,a)}return n.grep(a,function(a){return g.call(b,a)>=0!==c})}n.filter=function(a,b,c){var d=b[0];return c&&(a=":not("+a+")"),1===b.length&&1===d.nodeType?n.find.matchesSelector(d,a)?[d]:[]:n.find.matches(a,n.grep(b,function(a){return 1===a.nodeType}))},n.fn.extend({find:function(a){var b,c=this.length,d=[],e=this;if("string"!=typeof a)return this.pushStack(n(a).filter(function(){for(b=0;c>b;b++)if(n.contains(e[b],this))return!0}));for(b=0;c>b;b++)n.find(a,e[b],d);return d=this.pushStack(c>1?n.unique(d):d),d.selector=this.selector?this.selector+" "+a:a,d},filter:function(a){return this.pushStack(x(this,a||[],!1))},not:function(a){return this.pushStack(x(this,a||[],!0))},is:function(a){return!!x(this,"string"==typeof a&&u.test(a)?n(a):a||[],!1).length}});var y,z=/^(?:\s*(<[\w\W]+>)[^>]*|#([\w-]*))$/,A=n.fn.init=function(a,b){var c,d;if(!a)return this;if("string"==typeof a){if(c="<"===a[0]&&">"===a[a.length-1]&&a.length>=3?[null,a,null]:z.exec(a),!c||!c[1]&&b)return!b||b.jquery?(b||y).find(a):this.constructor(b).find(a);if(c[1]){if(b=b instanceof n?b[0]:b,n.merge(this,n.parseHTML(c[1],b&&b.nodeType?b.ownerDocument||b:l,!0)),v.test(c[1])&&n.isPlainObject(b))for(c in b)n.isFunction(this[c])?this[c](b[c]):this.attr(c,b[c]);return this}return d=l.getElementById(c[2]),d&&d.parentNode&&(this.length=1,this[0]=d),this.context=l,this.selector=a,this}return a.nodeType?(this.context=this[0]=a,this.length=1,this):n.isFunction(a)?"undefined"!=typeof y.ready?y.ready(a):a(n):(void 0!==a.selector&&(this.selector=a.selector,this.context=a.context),n.makeArray(a,this))};A.prototype=n.fn,y=n(l);var B=/^(?:parents|prev(?:Until|All))/,C={children:!0,contents:!0,next:!0,prev:!0};n.extend({dir:function(a,b,c){var d=[],e=void 0!==c;while((a=a[b])&&9!==a.nodeType)if(1===a.nodeType){if(e&&n(a).is(c))break;d.push(a)}return d},sibling:function(a,b){for(var c=[];a;a=a.nextSibling)1===a.nodeType&&a!==b&&c.push(a);return c}}),n.fn.extend({has:function(a){var b=n(a,this),c=b.length;return this.filter(function(){for(var a=0;c>a;a++)if(n.contains(this,b[a]))return!0})},closest:function(a,b){for(var c,d=0,e=this.length,f=[],g=u.test(a)||"string"!=typeof a?n(a,b||this.context):0;e>d;d++)for(c=this[d];c&&c!==b;c=c.parentNode)if(c.nodeType<11&&(g?g.index(c)>-1:1===c.nodeType&&n.find.matchesSelector(c,a))){f.push(c);break}return this.pushStack(f.length>1?n.unique(f):f)},index:function(a){return a?"string"==typeof a?g.call(n(a),this[0]):g.call(this,a.jquery?a[0]:a):this[0]&&this[0].parentNode?this.first().prevAll().length:-1},add:function(a,b){return this.pushStack(n.unique(n.merge(this.get(),n(a,b))))},addBack:function(a){return this.add(null==a?this.prevObject:this.prevObject.filter(a))}});function D(a,b){while((a=a[b])&&1!==a.nodeType);return a}n.each({parent:function(a){var b=a.parentNode;return b&&11!==b.nodeType?b:null},parents:function(a){return n.dir(a,"parentNode")},parentsUntil:function(a,b,c){return n.dir(a,"parentNode",c)},next:function(a){return D(a,"nextSibling")},prev:function(a){return D(a,"previousSibling")},nextAll:function(a){return n.dir(a,"nextSibling")},prevAll:function(a){return n.dir(a,"previousSibling")},nextUntil:function(a,b,c){return n.dir(a,"nextSibling",c)},prevUntil:function(a,b,c){return n.dir(a,"previousSibling",c)},siblings:function(a){return n.sibling((a.parentNode||{}).firstChild,a)},children:function(a){return n.sibling(a.firstChild)},contents:function(a){return a.contentDocument||n.merge([],a.childNodes)}},function(a,b){n.fn[a]=function(c,d){var e=n.map(this,b,c);return"Until"!==a.slice(-5)&&(d=c),d&&"string"==typeof d&&(e=n.filter(d,e)),this.length>1&&(C[a]||n.unique(e),B.test(a)&&e.reverse()),this.pushStack(e)}});var E=/\S+/g,F={};function G(a){var b=F[a]={};return n.each(a.match(E)||[],function(a,c){b[c]=!0}),b}n.Callbacks=function(a){a="string"==typeof a?F[a]||G(a):n.extend({},a);var b,c,d,e,f,g,h=[],i=!a.once&&[],j=function(l){for(b=a.memory&&l,c=!0,g=e||0,e=0,f=h.length,d=!0;h&&f>g;g++)if(h[g].apply(l[0],l[1])===!1&&a.stopOnFalse){b=!1;break}d=!1,h&&(i?i.length&&j(i.shift()):b?h=[]:k.disable())},k={add:function(){if(h){var c=h.length;!function g(b){n.each(b,function(b,c){var d=n.type(c);"function"===d?a.unique&&k.has(c)||h.push(c):c&&c.length&&"string"!==d&&g(c)})}(arguments),d?f=h.length:b&&(e=c,j(b))}return this},remove:function(){return h&&n.each(arguments,function(a,b){var c;while((c=n.inArray(b,h,c))>-1)h.splice(c,1),d&&(f>=c&&f--,g>=c&&g--)}),this},has:function(a){return a?n.inArray(a,h)>-1:!(!h||!h.length)},empty:function(){return h=[],f=0,this},disable:function(){return h=i=b=void 0,this},disabled:function(){return!h},lock:function(){return i=void 0,b||k.disable(),this},locked:function(){return!i},fireWith:function(a,b){return!h||c&&!i||(b=b||[],b=[a,b.slice?b.slice():b],d?i.push(b):j(b)),this},fire:function(){return k.fireWith(this,arguments),this},fired:function(){return!!c}};return k},n.extend({Deferred:function(a){var b=[["resolve","done",n.Callbacks("once memory"),"resolved"],["reject","fail",n.Callbacks("once memory"),"rejected"],["notify","progress",n.Callbacks("memory")]],c="pending",d={state:function(){return c},always:function(){return e.done(arguments).fail(arguments),this},then:function(){var a=arguments;return n.Deferred(function(c){n.each(b,function(b,f){var g=n.isFunction(a[b])&&a[b];e[f[1]](function(){var a=g&&g.apply(this,arguments);a&&n.isFunction(a.promise)?a.promise().done(c.resolve).fail(c.reject).progress(c.notify):c[f[0]+"With"](this===d?c.promise():this,g?[a]:arguments)})}),a=null}).promise()},promise:function(a){return null!=a?n.extend(a,d):d}},e={};return d.pipe=d.then,n.each(b,function(a,f){var g=f[2],h=f[3];d[f[1]]=g.add,h&&g.add(function(){c=h},b[1^a][2].disable,b[2][2].lock),e[f[0]]=function(){return e[f[0]+"With"](this===e?d:this,arguments),this},e[f[0]+"With"]=g.fireWith}),d.promise(e),a&&a.call(e,e),e},when:function(a){var b=0,c=d.call(arguments),e=c.length,f=1!==e||a&&n.isFunction(a.promise)?e:0,g=1===f?a:n.Deferred(),h=function(a,b,c){return function(e){b[a]=this,c[a]=arguments.length>1?d.call(arguments):e,c===i?g.notifyWith(b,c):--f||g.resolveWith(b,c)}},i,j,k;if(e>1)for(i=new Array(e),j=new Array(e),k=new Array(e);e>b;b++)c[b]&&n.isFunction(c[b].promise)?c[b].promise().done(h(b,k,c)).fail(g.reject).progress(h(b,j,i)):--f;return f||g.resolveWith(k,c),g.promise()}});var H;n.fn.ready=function(a){return n.ready.promise().done(a),this},n.extend({isReady:!1,readyWait:1,holdReady:function(a){a?n.readyWait++:n.ready(!0)},ready:function(a){(a===!0?--n.readyWait:n.isReady)||(n.isReady=!0,a!==!0&&--n.readyWait>0||(H.resolveWith(l,[n]),n.fn.triggerHandler&&(n(l).triggerHandler("ready"),n(l).off("ready"))))}});function I(){l.removeEventListener("DOMContentLoaded",I,!1),a.removeEventListener("load",I,!1),n.ready()}n.ready.promise=function(b){return H||(H=n.Deferred(),"complete"===l.readyState?setTimeout(n.ready):(l.addEventListener("DOMContentLoaded",I,!1),a.addEventListener("load",I,!1))),H.promise(b)},n.ready.promise();var J=n.access=function(a,b,c,d,e,f,g){var h=0,i=a.length,j=null==c;if("object"===n.type(c)){e=!0;for(h in c)n.access(a,b,h,c[h],!0,f,g)}else if(void 0!==d&&(e=!0,n.isFunction(d)||(g=!0),j&&(g?(b.call(a,d),b=null):(j=b,b=function(a,b,c){return j.call(n(a),c)})),b))for(;i>h;h++)b(a[h],c,g?d:d.call(a[h],h,b(a[h],c)));return e?a:j?b.call(a):i?b(a[0],c):f};n.acceptData=function(a){return 1===a.nodeType||9===a.nodeType||!+a.nodeType};function K(){Object.defineProperty(this.cache={},0,{get:function(){return{}}}),this.expando=n.expando+K.uid++}K.uid=1,K.accepts=n.acceptData,K.prototype={key:function(a){if(!K.accepts(a))return 0;var b={},c=a[this.expando];if(!c){c=K.uid++;try{b[this.expando]={value:c},Object.defineProperties(a,b)}catch(d){b[this.expando]=c,n.extend(a,b)}}return this.cache[c]||(this.cache[c]={}),c},set:function(a,b,c){var d,e=this.key(a),f=this.cache[e];if("string"==typeof b)f[b]=c;else if(n.isEmptyObject(f))n.extend(this.cache[e],b);else for(d in b)f[d]=b[d];return f},get:function(a,b){var c=this.cache[this.key(a)];return void 0===b?c:c[b]},access:function(a,b,c){var d;return void 0===b||b&&"string"==typeof b&&void 0===c?(d=this.get(a,b),void 0!==d?d:this.get(a,n.camelCase(b))):(this.set(a,b,c),void 0!==c?c:b)},remove:function(a,b){var c,d,e,f=this.key(a),g=this.cache[f];if(void 0===b)this.cache[f]={};else{n.isArray(b)?d=b.concat(b.map(n.camelCase)):(e=n.camelCase(b),b in g?d=[b,e]:(d=e,d=d in g?[d]:d.match(E)||[])),c=d.length;while(c--)delete g[d[c]]}},hasData:function(a){return!n.isEmptyObject(this.cache[a[this.expando]]||{})},discard:function(a){a[this.expando]&&delete this.cache[a[this.expando]]}};var L=new K,M=new K,N=/^(?:\{[\w\W]*\}|\[[\w\W]*\])$/,O=/([A-Z])/g;function P(a,b,c){var d;if(void 0===c&&1===a.nodeType)if(d="data-"+b.replace(O,"-$1").toLowerCase(),c=a.getAttribute(d),"string"==typeof c){try{c="true"===c?!0:"false"===c?!1:"null"===c?null:+c+""===c?+c:N.test(c)?n.parseJSON(c):c}catch(e){}M.set(a,b,c)}else c=void 0;return c}n.extend({hasData:function(a){return M.hasData(a)||L.hasData(a)},data:function(a,b,c){
return M.access(a,b,c)},removeData:function(a,b){M.remove(a,b)},_data:function(a,b,c){return L.access(a,b,c)},_removeData:function(a,b){L.remove(a,b)}}),n.fn.extend({data:function(a,b){var c,d,e,f=this[0],g=f&&f.attributes;if(void 0===a){if(this.length&&(e=M.get(f),1===f.nodeType&&!L.get(f,"hasDataAttrs"))){c=g.length;while(c--)g[c]&&(d=g[c].name,0===d.indexOf("data-")&&(d=n.camelCase(d.slice(5)),P(f,d,e[d])));L.set(f,"hasDataAttrs",!0)}return e}return"object"==typeof a?this.each(function(){M.set(this,a)}):J(this,function(b){var c,d=n.camelCase(a);if(f&&void 0===b){if(c=M.get(f,a),void 0!==c)return c;if(c=M.get(f,d),void 0!==c)return c;if(c=P(f,d,void 0),void 0!==c)return c}else this.each(function(){var c=M.get(this,d);M.set(this,d,b),-1!==a.indexOf("-")&&void 0!==c&&M.set(this,a,b)})},null,b,arguments.length>1,null,!0)},removeData:function(a){return this.each(function(){M.remove(this,a)})}}),n.extend({queue:function(a,b,c){var d;return a?(b=(b||"fx")+"queue",d=L.get(a,b),c&&(!d||n.isArray(c)?d=L.access(a,b,n.makeArray(c)):d.push(c)),d||[]):void 0},dequeue:function(a,b){b=b||"fx";var c=n.queue(a,b),d=c.length,e=c.shift(),f=n._queueHooks(a,b),g=function(){n.dequeue(a,b)};"inprogress"===e&&(e=c.shift(),d--),e&&("fx"===b&&c.unshift("inprogress"),delete f.stop,e.call(a,g,f)),!d&&f&&f.empty.fire()},_queueHooks:function(a,b){var c=b+"queueHooks";return L.get(a,c)||L.access(a,c,{empty:n.Callbacks("once memory").add(function(){L.remove(a,[b+"queue",c])})})}}),n.fn.extend({queue:function(a,b){var c=2;return"string"!=typeof a&&(b=a,a="fx",c--),arguments.length<c?n.queue(this[0],a):void 0===b?this:this.each(function(){var c=n.queue(this,a,b);n._queueHooks(this,a),"fx"===a&&"inprogress"!==c[0]&&n.dequeue(this,a)})},dequeue:function(a){return this.each(function(){n.dequeue(this,a)})},clearQueue:function(a){return this.queue(a||"fx",[])},promise:function(a,b){var c,d=1,e=n.Deferred(),f=this,g=this.length,h=function(){--d||e.resolveWith(f,[f])};"string"!=typeof a&&(b=a,a=void 0),a=a||"fx";while(g--)c=L.get(f[g],a+"queueHooks"),c&&c.empty&&(d++,c.empty.add(h));return h(),e.promise(b)}});var Q=/[+-]?(?:\d*\.|)\d+(?:[eE][+-]?\d+|)/.source,R=["Top","Right","Bottom","Left"],S=function(a,b){return a=b||a,"none"===n.css(a,"display")||!n.contains(a.ownerDocument,a)},T=/^(?:checkbox|radio)$/i;!function(){var a=l.createDocumentFragment(),b=a.appendChild(l.createElement("div")),c=l.createElement("input");c.setAttribute("type","radio"),c.setAttribute("checked","checked"),c.setAttribute("name","t"),b.appendChild(c),k.checkClone=b.cloneNode(!0).cloneNode(!0).lastChild.checked,b.innerHTML="<textarea>x</textarea>",k.noCloneChecked=!!b.cloneNode(!0).lastChild.defaultValue}();var U="undefined";k.focusinBubbles="onfocusin"in a;var V=/^key/,W=/^(?:mouse|pointer|contextmenu)|click/,X=/^(?:focusinfocus|focusoutblur)$/,Y=/^([^.]*)(?:\.(.+)|)$/;function Z(){return!0}function $(){return!1}function _(){try{return l.activeElement}catch(a){}}n.event={global:{},add:function(a,b,c,d,e){var f,g,h,i,j,k,l,m,o,p,q,r=L.get(a);if(r){c.handler&&(f=c,c=f.handler,e=f.selector),c.guid||(c.guid=n.guid++),(i=r.events)||(i=r.events={}),(g=r.handle)||(g=r.handle=function(b){return typeof n!==U&&n.event.triggered!==b.type?n.event.dispatch.apply(a,arguments):void 0}),b=(b||"").match(E)||[""],j=b.length;while(j--)h=Y.exec(b[j])||[],o=q=h[1],p=(h[2]||"").split(".").sort(),o&&(l=n.event.special[o]||{},o=(e?l.delegateType:l.bindType)||o,l=n.event.special[o]||{},k=n.extend({type:o,origType:q,data:d,handler:c,guid:c.guid,selector:e,needsContext:e&&n.expr.match.needsContext.test(e),namespace:p.join(".")},f),(m=i[o])||(m=i[o]=[],m.delegateCount=0,l.setup&&l.setup.call(a,d,p,g)!==!1||a.addEventListener&&a.addEventListener(o,g,!1)),l.add&&(l.add.call(a,k),k.handler.guid||(k.handler.guid=c.guid)),e?m.splice(m.delegateCount++,0,k):m.push(k),n.event.global[o]=!0)}},remove:function(a,b,c,d,e){var f,g,h,i,j,k,l,m,o,p,q,r=L.hasData(a)&&L.get(a);if(r&&(i=r.events)){b=(b||"").match(E)||[""],j=b.length;while(j--)if(h=Y.exec(b[j])||[],o=q=h[1],p=(h[2]||"").split(".").sort(),o){l=n.event.special[o]||{},o=(d?l.delegateType:l.bindType)||o,m=i[o]||[],h=h[2]&&new RegExp("(^|\\.)"+p.join("\\.(?:.*\\.|)")+"(\\.|$)"),g=f=m.length;while(f--)k=m[f],!e&&q!==k.origType||c&&c.guid!==k.guid||h&&!h.test(k.namespace)||d&&d!==k.selector&&("**"!==d||!k.selector)||(m.splice(f,1),k.selector&&m.delegateCount--,l.remove&&l.remove.call(a,k));g&&!m.length&&(l.teardown&&l.teardown.call(a,p,r.handle)!==!1||n.removeEvent(a,o,r.handle),delete i[o])}else for(o in i)n.event.remove(a,o+b[j],c,d,!0);n.isEmptyObject(i)&&(delete r.handle,L.remove(a,"events"))}},trigger:function(b,c,d,e){var f,g,h,i,k,m,o,p=[d||l],q=j.call(b,"type")?b.type:b,r=j.call(b,"namespace")?b.namespace.split("."):[];if(g=h=d=d||l,3!==d.nodeType&&8!==d.nodeType&&!X.test(q+n.event.triggered)&&(q.indexOf(".")>=0&&(r=q.split("."),q=r.shift(),r.sort()),k=q.indexOf(":")<0&&"on"+q,b=b[n.expando]?b:new n.Event(q,"object"==typeof b&&b),b.isTrigger=e?2:3,b.namespace=r.join("."),b.namespace_re=b.namespace?new RegExp("(^|\\.)"+r.join("\\.(?:.*\\.|)")+"(\\.|$)"):null,b.result=void 0,b.target||(b.target=d),c=null==c?[b]:n.makeArray(c,[b]),o=n.event.special[q]||{},e||!o.trigger||o.trigger.apply(d,c)!==!1)){if(!e&&!o.noBubble&&!n.isWindow(d)){for(i=o.delegateType||q,X.test(i+q)||(g=g.parentNode);g;g=g.parentNode)p.push(g),h=g;h===(d.ownerDocument||l)&&p.push(h.defaultView||h.parentWindow||a)}f=0;while((g=p[f++])&&!b.isPropagationStopped())b.type=f>1?i:o.bindType||q,m=(L.get(g,"events")||{})[b.type]&&L.get(g,"handle"),m&&m.apply(g,c),m=k&&g[k],m&&m.apply&&n.acceptData(g)&&(b.result=m.apply(g,c),b.result===!1&&b.preventDefault());return b.type=q,e||b.isDefaultPrevented()||o._default&&o._default.apply(p.pop(),c)!==!1||!n.acceptData(d)||k&&n.isFunction(d[q])&&!n.isWindow(d)&&(h=d[k],h&&(d[k]=null),n.event.triggered=q,d[q](),n.event.triggered=void 0,h&&(d[k]=h)),b.result}},dispatch:function(a){a=n.event.fix(a);var b,c,e,f,g,h=[],i=d.call(arguments),j=(L.get(this,"events")||{})[a.type]||[],k=n.event.special[a.type]||{};if(i[0]=a,a.delegateTarget=this,!k.preDispatch||k.preDispatch.call(this,a)!==!1){h=n.event.handlers.call(this,a,j),b=0;while((f=h[b++])&&!a.isPropagationStopped()){a.currentTarget=f.elem,c=0;while((g=f.handlers[c++])&&!a.isImmediatePropagationStopped())(!a.namespace_re||a.namespace_re.test(g.namespace))&&(a.handleObj=g,a.data=g.data,e=((n.event.special[g.origType]||{}).handle||g.handler).apply(f.elem,i),void 0!==e&&(a.result=e)===!1&&(a.preventDefault(),a.stopPropagation()))}return k.postDispatch&&k.postDispatch.call(this,a),a.result}},handlers:function(a,b){var c,d,e,f,g=[],h=b.delegateCount,i=a.target;if(h&&i.nodeType&&(!a.button||"click"!==a.type))for(;i!==this;i=i.parentNode||this)if(i.disabled!==!0||"click"!==a.type){for(d=[],c=0;h>c;c++)f=b[c],e=f.selector+" ",void 0===d[e]&&(d[e]=f.needsContext?n(e,this).index(i)>=0:n.find(e,this,null,[i]).length),d[e]&&d.push(f);d.length&&g.push({elem:i,handlers:d})}return h<b.length&&g.push({elem:this,handlers:b.slice(h)}),g},props:"altKey bubbles cancelable ctrlKey currentTarget eventPhase metaKey relatedTarget shiftKey target timeStamp view which".split(" "),fixHooks:{},keyHooks:{props:"char charCode key keyCode".split(" "),filter:function(a,b){return null==a.which&&(a.which=null!=b.charCode?b.charCode:b.keyCode),a}},mouseHooks:{props:"button buttons clientX clientY offsetX offsetY pageX pageY screenX screenY toElement".split(" "),filter:function(a,b){var c,d,e,f=b.button;return null==a.pageX&&null!=b.clientX&&(c=a.target.ownerDocument||l,d=c.documentElement,e=c.body,a.pageX=b.clientX+(d&&d.scrollLeft||e&&e.scrollLeft||0)-(d&&d.clientLeft||e&&e.clientLeft||0),a.pageY=b.clientY+(d&&d.scrollTop||e&&e.scrollTop||0)-(d&&d.clientTop||e&&e.clientTop||0)),a.which||void 0===f||(a.which=1&f?1:2&f?3:4&f?2:0),a}},fix:function(a){if(a[n.expando])return a;var b,c,d,e=a.type,f=a,g=this.fixHooks[e];g||(this.fixHooks[e]=g=W.test(e)?this.mouseHooks:V.test(e)?this.keyHooks:{}),d=g.props?this.props.concat(g.props):this.props,a=new n.Event(f),b=d.length;while(b--)c=d[b],a[c]=f[c];return a.target||(a.target=l),3===a.target.nodeType&&(a.target=a.target.parentNode),g.filter?g.filter(a,f):a},special:{load:{noBubble:!0},focus:{trigger:function(){return this!==_()&&this.focus?(this.focus(),!1):void 0},delegateType:"focusin"},blur:{trigger:function(){return this===_()&&this.blur?(this.blur(),!1):void 0},delegateType:"focusout"},click:{trigger:function(){return"checkbox"===this.type&&this.click&&n.nodeName(this,"input")?(this.click(),!1):void 0},_default:function(a){return n.nodeName(a.target,"a")}},beforeunload:{postDispatch:function(a){void 0!==a.result&&a.originalEvent&&(a.originalEvent.returnValue=a.result)}}},simulate:function(a,b,c,d){var e=n.extend(new n.Event,c,{type:a,isSimulated:!0,originalEvent:{}});d?n.event.trigger(e,null,b):n.event.dispatch.call(b,e),e.isDefaultPrevented()&&c.preventDefault()}},n.removeEvent=function(a,b,c){a.removeEventListener&&a.removeEventListener(b,c,!1)},n.Event=function(a,b){return this instanceof n.Event?(a&&a.type?(this.originalEvent=a,this.type=a.type,this.isDefaultPrevented=a.defaultPrevented||void 0===a.defaultPrevented&&a.returnValue===!1?Z:$):this.type=a,b&&n.extend(this,b),this.timeStamp=a&&a.timeStamp||n.now(),void(this[n.expando]=!0)):new n.Event(a,b)},n.Event.prototype={isDefaultPrevented:$,isPropagationStopped:$,isImmediatePropagationStopped:$,preventDefault:function(){var a=this.originalEvent;this.isDefaultPrevented=Z,a&&a.preventDefault&&a.preventDefault()},stopPropagation:function(){var a=this.originalEvent;this.isPropagationStopped=Z,a&&a.stopPropagation&&a.stopPropagation()},stopImmediatePropagation:function(){var a=this.originalEvent;this.isImmediatePropagationStopped=Z,a&&a.stopImmediatePropagation&&a.stopImmediatePropagation(),this.stopPropagation()}},n.each({mouseenter:"mouseover",mouseleave:"mouseout",pointerenter:"pointerover",pointerleave:"pointerout"},function(a,b){n.event.special[a]={delegateType:b,bindType:b,handle:function(a){var c,d=this,e=a.relatedTarget,f=a.handleObj;return(!e||e!==d&&!n.contains(d,e))&&(a.type=f.origType,c=f.handler.apply(this,arguments),a.type=b),c}}}),k.focusinBubbles||n.each({focus:"focusin",blur:"focusout"},function(a,b){var c=function(a){n.event.simulate(b,a.target,n.event.fix(a),!0)};n.event.special[b]={setup:function(){var d=this.ownerDocument||this,e=L.access(d,b);e||d.addEventListener(a,c,!0),L.access(d,b,(e||0)+1)},teardown:function(){var d=this.ownerDocument||this,e=L.access(d,b)-1;e?L.access(d,b,e):(d.removeEventListener(a,c,!0),L.remove(d,b))}}}),n.fn.extend({on:function(a,b,c,d,e){var f,g;if("object"==typeof a){"string"!=typeof b&&(c=c||b,b=void 0);for(g in a)this.on(g,b,c,a[g],e);return this}if(null==c&&null==d?(d=b,c=b=void 0):null==d&&("string"==typeof b?(d=c,c=void 0):(d=c,c=b,b=void 0)),d===!1)d=$;else if(!d)return this;return 1===e&&(f=d,d=function(a){return n().off(a),f.apply(this,arguments)},d.guid=f.guid||(f.guid=n.guid++)),this.each(function(){n.event.add(this,a,d,c,b)})},one:function(a,b,c,d){return this.on(a,b,c,d,1)},off:function(a,b,c){var d,e;if(a&&a.preventDefault&&a.handleObj)return d=a.handleObj,n(a.delegateTarget).off(d.namespace?d.origType+"."+d.namespace:d.origType,d.selector,d.handler),this;if("object"==typeof a){for(e in a)this.off(e,b,a[e]);return this}return(b===!1||"function"==typeof b)&&(c=b,b=void 0),c===!1&&(c=$),this.each(function(){n.event.remove(this,a,c,b)})},trigger:function(a,b){return this.each(function(){n.event.trigger(a,b,this)})},triggerHandler:function(a,b){var c=this[0];return c?n.event.trigger(a,b,c,!0):void 0}});var aa=/<(?!area|br|col|embed|hr|img|input|link|meta|param)(([\w:]+)[^>]*)\/>/gi,ba=/<([\w:]+)/,ca=/<|&#?\w+;/,da=/<(?:script|style|link)/i,ea=/checked\s*(?:[^=]|=\s*.checked.)/i,fa=/^$|\/(?:java|ecma)script/i,ga=/^true\/(.*)/,ha=/^\s*<!(?:\[CDATA\[|--)|(?:\]\]|--)>\s*$/g,ia={option:[1,"<select multiple='multiple'>","</select>"],thead:[1,"<table>","</table>"],col:[2,"<table><colgroup>","</colgroup></table>"],tr:[2,"<table><tbody>","</tbody></table>"],td:[3,"<table><tbody><tr>","</tr></tbody></table>"],_default:[0,"",""]};ia.optgroup=ia.option,ia.tbody=ia.tfoot=ia.colgroup=ia.caption=ia.thead,ia.th=ia.td;function ja(a,b){return n.nodeName(a,"table")&&n.nodeName(11!==b.nodeType?b:b.firstChild,"tr")?a.getElementsByTagName("tbody")[0]||a.appendChild(a.ownerDocument.createElement("tbody")):a}function ka(a){return a.type=(null!==a.getAttribute("type"))+"/"+a.type,a}function la(a){var b=ga.exec(a.type);return b?a.type=b[1]:a.removeAttribute("type"),a}function ma(a,b){for(var c=0,d=a.length;d>c;c++)L.set(a[c],"globalEval",!b||L.get(b[c],"globalEval"))}function na(a,b){var c,d,e,f,g,h,i,j;if(1===b.nodeType){if(L.hasData(a)&&(f=L.access(a),g=L.set(b,f),j=f.events)){delete g.handle,g.events={};for(e in j)for(c=0,d=j[e].length;d>c;c++)n.event.add(b,e,j[e][c])}M.hasData(a)&&(h=M.access(a),i=n.extend({},h),M.set(b,i))}}function oa(a,b){var c=a.getElementsByTagName?a.getElementsByTagName(b||"*"):a.querySelectorAll?a.querySelectorAll(b||"*"):[];return void 0===b||b&&n.nodeName(a,b)?n.merge([a],c):c}function pa(a,b){var c=b.nodeName.toLowerCase();"input"===c&&T.test(a.type)?b.checked=a.checked:("input"===c||"textarea"===c)&&(b.defaultValue=a.defaultValue)}n.extend({clone:function(a,b,c){var d,e,f,g,h=a.cloneNode(!0),i=n.contains(a.ownerDocument,a);if(!(k.noCloneChecked||1!==a.nodeType&&11!==a.nodeType||n.isXMLDoc(a)))for(g=oa(h),f=oa(a),d=0,e=f.length;e>d;d++)pa(f[d],g[d]);if(b)if(c)for(f=f||oa(a),g=g||oa(h),d=0,e=f.length;e>d;d++)na(f[d],g[d]);else na(a,h);return g=oa(h,"script"),g.length>0&&ma(g,!i&&oa(a,"script")),h},buildFragment:function(a,b,c,d){for(var e,f,g,h,i,j,k=b.createDocumentFragment(),l=[],m=0,o=a.length;o>m;m++)if(e=a[m],e||0===e)if("object"===n.type(e))n.merge(l,e.nodeType?[e]:e);else if(ca.test(e)){f=f||k.appendChild(b.createElement("div")),g=(ba.exec(e)||["",""])[1].toLowerCase(),h=ia[g]||ia._default,f.innerHTML=h[1]+e.replace(aa,"<$1></$2>")+h[2],j=h[0];while(j--)f=f.lastChild;n.merge(l,f.childNodes),f=k.firstChild,f.textContent=""}else l.push(b.createTextNode(e));k.textContent="",m=0;while(e=l[m++])if((!d||-1===n.inArray(e,d))&&(i=n.contains(e.ownerDocument,e),f=oa(k.appendChild(e),"script"),i&&ma(f),c)){j=0;while(e=f[j++])fa.test(e.type||"")&&c.push(e)}return k},cleanData:function(a){for(var b,c,d,e,f=n.event.special,g=0;void 0!==(c=a[g]);g++){if(n.acceptData(c)&&(e=c[L.expando],e&&(b=L.cache[e]))){if(b.events)for(d in b.events)f[d]?n.event.remove(c,d):n.removeEvent(c,d,b.handle);L.cache[e]&&delete L.cache[e]}delete M.cache[c[M.expando]]}}}),n.fn.extend({text:function(a){return J(this,function(a){return void 0===a?n.text(this):this.empty().each(function(){(1===this.nodeType||11===this.nodeType||9===this.nodeType)&&(this.textContent=a)})},null,a,arguments.length)},append:function(){return this.domManip(arguments,function(a){if(1===this.nodeType||11===this.nodeType||9===this.nodeType){var b=ja(this,a);b.appendChild(a)}})},prepend:function(){return this.domManip(arguments,function(a){if(1===this.nodeType||11===this.nodeType||9===this.nodeType){var b=ja(this,a);b.insertBefore(a,b.firstChild)}})},before:function(){return this.domManip(arguments,function(a){this.parentNode&&this.parentNode.insertBefore(a,this)})},after:function(){return this.domManip(arguments,function(a){this.parentNode&&this.parentNode.insertBefore(a,this.nextSibling)})},remove:function(a,b){for(var c,d=a?n.filter(a,this):this,e=0;null!=(c=d[e]);e++)b||1!==c.nodeType||n.cleanData(oa(c)),c.parentNode&&(b&&n.contains(c.ownerDocument,c)&&ma(oa(c,"script")),c.parentNode.removeChild(c));return this},empty:function(){for(var a,b=0;null!=(a=this[b]);b++)1===a.nodeType&&(n.cleanData(oa(a,!1)),a.textContent="");return this},clone:function(a,b){return a=null==a?!1:a,b=null==b?a:b,this.map(function(){return n.clone(this,a,b)})},html:function(a){return J(this,function(a){var b=this[0]||{},c=0,d=this.length;if(void 0===a&&1===b.nodeType)return b.innerHTML;if("string"==typeof a&&!da.test(a)&&!ia[(ba.exec(a)||["",""])[1].toLowerCase()]){a=a.replace(aa,"<$1></$2>");try{for(;d>c;c++)b=this[c]||{},1===b.nodeType&&(n.cleanData(oa(b,!1)),b.innerHTML=a);b=0}catch(e){}}b&&this.empty().append(a)},null,a,arguments.length)},replaceWith:function(){var a=arguments[0];return this.domManip(arguments,function(b){a=this.parentNode,n.cleanData(oa(this)),a&&a.replaceChild(b,this)}),a&&(a.length||a.nodeType)?this:this.remove()},detach:function(a){return this.remove(a,!0)},domManip:function(a,b){a=e.apply([],a);var c,d,f,g,h,i,j=0,l=this.length,m=this,o=l-1,p=a[0],q=n.isFunction(p);if(q||l>1&&"string"==typeof p&&!k.checkClone&&ea.test(p))return this.each(function(c){var d=m.eq(c);q&&(a[0]=p.call(this,c,d.html())),d.domManip(a,b)});if(l&&(c=n.buildFragment(a,this[0].ownerDocument,!1,this),d=c.firstChild,1===c.childNodes.length&&(c=d),d)){for(f=n.map(oa(c,"script"),ka),g=f.length;l>j;j++)h=c,j!==o&&(h=n.clone(h,!0,!0),g&&n.merge(f,oa(h,"script"))),b.call(this[j],h,j);if(g)for(i=f[f.length-1].ownerDocument,n.map(f,la),j=0;g>j;j++)h=f[j],fa.test(h.type||"")&&!L.access(h,"globalEval")&&n.contains(i,h)&&(h.src?n._evalUrl&&n._evalUrl(h.src):n.globalEval(h.textContent.replace(ha,"")))}return this}}),n.each({appendTo:"append",prependTo:"prepend",insertBefore:"before",insertAfter:"after",replaceAll:"replaceWith"},function(a,b){n.fn[a]=function(a){for(var c,d=[],e=n(a),g=e.length-1,h=0;g>=h;h++)c=h===g?this:this.clone(!0),n(e[h])[b](c),f.apply(d,c.get());return this.pushStack(d)}});var qa,ra={};function sa(b,c){var d,e=n(c.createElement(b)).appendTo(c.body),f=a.getDefaultComputedStyle&&(d=a.getDefaultComputedStyle(e[0]))?d.display:n.css(e[0],"display");return e.detach(),f}function ta(a){var b=l,c=ra[a];return c||(c=sa(a,b),"none"!==c&&c||(qa=(qa||n("<iframe frameborder='0' width='0' height='0'/>")).appendTo(b.documentElement),b=qa[0].contentDocument,b.write(),b.close(),c=sa(a,b),qa.detach()),ra[a]=c),c}var ua=/^margin/,va=new RegExp("^("+Q+")(?!px)[a-z%]+$","i"),wa=function(b){return b.ownerDocument.defaultView.opener?b.ownerDocument.defaultView.getComputedStyle(b,null):a.getComputedStyle(b,null)};function xa(a,b,c){var d,e,f,g,h=a.style;return c=c||wa(a),c&&(g=c.getPropertyValue(b)||c[b]),c&&(""!==g||n.contains(a.ownerDocument,a)||(g=n.style(a,b)),va.test(g)&&ua.test(b)&&(d=h.width,e=h.minWidth,f=h.maxWidth,h.minWidth=h.maxWidth=h.width=g,g=c.width,h.width=d,h.minWidth=e,h.maxWidth=f)),void 0!==g?g+"":g}function ya(a,b){return{get:function(){return a()?void delete this.get:(this.get=b).apply(this,arguments)}}}!function(){var b,c,d=l.documentElement,e=l.createElement("div"),f=l.createElement("div");if(f.style){f.style.backgroundClip="content-box",f.cloneNode(!0).style.backgroundClip="",k.clearCloneStyle="content-box"===f.style.backgroundClip,e.style.cssText="border:0;width:0;height:0;top:0;left:-9999px;margin-top:1px;position:absolute",e.appendChild(f);function g(){f.style.cssText="-webkit-box-sizing:border-box;-moz-box-sizing:border-box;box-sizing:border-box;display:block;margin-top:1%;top:1%;border:1px;padding:1px;width:4px;position:absolute",f.innerHTML="",d.appendChild(e);var g=a.getComputedStyle(f,null);b="1%"!==g.top,c="4px"===g.width,d.removeChild(e)}a.getComputedStyle&&n.extend(k,{pixelPosition:function(){return g(),b},boxSizingReliable:function(){return null==c&&g(),c},reliableMarginRight:function(){var b,c=f.appendChild(l.createElement("div"));return c.style.cssText=f.style.cssText="-webkit-box-sizing:content-box;-moz-box-sizing:content-box;box-sizing:content-box;display:block;margin:0;border:0;padding:0",c.style.marginRight=c.style.width="0",f.style.width="1px",d.appendChild(e),b=!parseFloat(a.getComputedStyle(c,null).marginRight),d.removeChild(e),f.removeChild(c),b}})}}(),n.swap=function(a,b,c,d){var e,f,g={};for(f in b)g[f]=a.style[f],a.style[f]=b[f];e=c.apply(a,d||[]);for(f in b)a.style[f]=g[f];return e};var za=/^(none|table(?!-c[ea]).+)/,Aa=new RegExp("^("+Q+")(.*)$","i"),Ba=new RegExp("^([+-])=("+Q+")","i"),Ca={position:"absolute",visibility:"hidden",display:"block"},Da={letterSpacing:"0",fontWeight:"400"},Ea=["Webkit","O","Moz","ms"];function Fa(a,b){if(b in a)return b;var c=b[0].toUpperCase()+b.slice(1),d=b,e=Ea.length;while(e--)if(b=Ea[e]+c,b in a)return b;return d}function Ga(a,b,c){var d=Aa.exec(b);return d?Math.max(0,d[1]-(c||0))+(d[2]||"px"):b}function Ha(a,b,c,d,e){for(var f=c===(d?"border":"content")?4:"width"===b?1:0,g=0;4>f;f+=2)"margin"===c&&(g+=n.css(a,c+R[f],!0,e)),d?("content"===c&&(g-=n.css(a,"padding"+R[f],!0,e)),"margin"!==c&&(g-=n.css(a,"border"+R[f]+"Width",!0,e))):(g+=n.css(a,"padding"+R[f],!0,e),"padding"!==c&&(g+=n.css(a,"border"+R[f]+"Width",!0,e)));return g}function Ia(a,b,c){var d=!0,e="width"===b?a.offsetWidth:a.offsetHeight,f=wa(a),g="border-box"===n.css(a,"boxSizing",!1,f);if(0>=e||null==e){if(e=xa(a,b,f),(0>e||null==e)&&(e=a.style[b]),va.test(e))return e;d=g&&(k.boxSizingReliable()||e===a.style[b]),e=parseFloat(e)||0}return e+Ha(a,b,c||(g?"border":"content"),d,f)+"px"}function Ja(a,b){for(var c,d,e,f=[],g=0,h=a.length;h>g;g++)d=a[g],d.style&&(f[g]=L.get(d,"olddisplay"),c=d.style.display,b?(f[g]||"none"!==c||(d.style.display=""),""===d.style.display&&S(d)&&(f[g]=L.access(d,"olddisplay",ta(d.nodeName)))):(e=S(d),"none"===c&&e||L.set(d,"olddisplay",e?c:n.css(d,"display"))));for(g=0;h>g;g++)d=a[g],d.style&&(b&&"none"!==d.style.display&&""!==d.style.display||(d.style.display=b?f[g]||"":"none"));return a}n.extend({cssHooks:{opacity:{get:function(a,b){if(b){var c=xa(a,"opacity");return""===c?"1":c}}}},cssNumber:{columnCount:!0,fillOpacity:!0,flexGrow:!0,flexShrink:!0,fontWeight:!0,lineHeight:!0,opacity:!0,order:!0,orphans:!0,widows:!0,zIndex:!0,zoom:!0},cssProps:{"float":"cssFloat"},style:function(a,b,c,d){if(a&&3!==a.nodeType&&8!==a.nodeType&&a.style){var e,f,g,h=n.camelCase(b),i=a.style;return b=n.cssProps[h]||(n.cssProps[h]=Fa(i,h)),g=n.cssHooks[b]||n.cssHooks[h],void 0===c?g&&"get"in g&&void 0!==(e=g.get(a,!1,d))?e:i[b]:(f=typeof c,"string"===f&&(e=Ba.exec(c))&&(c=(e[1]+1)*e[2]+parseFloat(n.css(a,b)),f="number"),null!=c&&c===c&&("number"!==f||n.cssNumber[h]||(c+="px"),k.clearCloneStyle||""!==c||0!==b.indexOf("background")||(i[b]="inherit"),g&&"set"in g&&void 0===(c=g.set(a,c,d))||(i[b]=c)),void 0)}},css:function(a,b,c,d){var e,f,g,h=n.camelCase(b);return b=n.cssProps[h]||(n.cssProps[h]=Fa(a.style,h)),g=n.cssHooks[b]||n.cssHooks[h],g&&"get"in g&&(e=g.get(a,!0,c)),void 0===e&&(e=xa(a,b,d)),"normal"===e&&b in Da&&(e=Da[b]),""===c||c?(f=parseFloat(e),c===!0||n.isNumeric(f)?f||0:e):e}}),n.each(["height","width"],function(a,b){n.cssHooks[b]={get:function(a,c,d){return c?za.test(n.css(a,"display"))&&0===a.offsetWidth?n.swap(a,Ca,function(){return Ia(a,b,d)}):Ia(a,b,d):void 0},set:function(a,c,d){var e=d&&wa(a);return Ga(a,c,d?Ha(a,b,d,"border-box"===n.css(a,"boxSizing",!1,e),e):0)}}}),n.cssHooks.marginRight=ya(k.reliableMarginRight,function(a,b){return b?n.swap(a,{display:"inline-block"},xa,[a,"marginRight"]):void 0}),n.each({margin:"",padding:"",border:"Width"},function(a,b){n.cssHooks[a+b]={expand:function(c){for(var d=0,e={},f="string"==typeof c?c.split(" "):[c];4>d;d++)e[a+R[d]+b]=f[d]||f[d-2]||f[0];return e}},ua.test(a)||(n.cssHooks[a+b].set=Ga)}),n.fn.extend({css:function(a,b){return J(this,function(a,b,c){var d,e,f={},g=0;if(n.isArray(b)){for(d=wa(a),e=b.length;e>g;g++)f[b[g]]=n.css(a,b[g],!1,d);return f}return void 0!==c?n.style(a,b,c):n.css(a,b)},a,b,arguments.length>1)},show:function(){return Ja(this,!0)},hide:function(){return Ja(this)},toggle:function(a){return"boolean"==typeof a?a?this.show():this.hide():this.each(function(){S(this)?n(this).show():n(this).hide()})}});function Ka(a,b,c,d,e){return new Ka.prototype.init(a,b,c,d,e)}n.Tween=Ka,Ka.prototype={constructor:Ka,init:function(a,b,c,d,e,f){this.elem=a,this.prop=c,this.easing=e||"swing",this.options=b,this.start=this.now=this.cur(),this.end=d,this.unit=f||(n.cssNumber[c]?"":"px")},cur:function(){var a=Ka.propHooks[this.prop];return a&&a.get?a.get(this):Ka.propHooks._default.get(this)},run:function(a){var b,c=Ka.propHooks[this.prop];return this.options.duration?this.pos=b=n.easing[this.easing](a,this.options.duration*a,0,1,this.options.duration):this.pos=b=a,this.now=(this.end-this.start)*b+this.start,this.options.step&&this.options.step.call(this.elem,this.now,this),c&&c.set?c.set(this):Ka.propHooks._default.set(this),this}},Ka.prototype.init.prototype=Ka.prototype,Ka.propHooks={_default:{get:function(a){var b;return null==a.elem[a.prop]||a.elem.style&&null!=a.elem.style[a.prop]?(b=n.css(a.elem,a.prop,""),b&&"auto"!==b?b:0):a.elem[a.prop]},set:function(a){n.fx.step[a.prop]?n.fx.step[a.prop](a):a.elem.style&&(null!=a.elem.style[n.cssProps[a.prop]]||n.cssHooks[a.prop])?n.style(a.elem,a.prop,a.now+a.unit):a.elem[a.prop]=a.now}}},Ka.propHooks.scrollTop=Ka.propHooks.scrollLeft={set:function(a){a.elem.nodeType&&a.elem.parentNode&&(a.elem[a.prop]=a.now)}},n.easing={linear:function(a){return a},swing:function(a){return.5-Math.cos(a*Math.PI)/2}},n.fx=Ka.prototype.init,n.fx.step={};var La,Ma,Na=/^(?:toggle|show|hide)$/,Oa=new RegExp("^(?:([+-])=|)("+Q+")([a-z%]*)$","i"),Pa=/queueHooks$/,Qa=[Va],Ra={"*":[function(a,b){var c=this.createTween(a,b),d=c.cur(),e=Oa.exec(b),f=e&&e[3]||(n.cssNumber[a]?"":"px"),g=(n.cssNumber[a]||"px"!==f&&+d)&&Oa.exec(n.css(c.elem,a)),h=1,i=20;if(g&&g[3]!==f){f=f||g[3],e=e||[],g=+d||1;do h=h||".5",g/=h,n.style(c.elem,a,g+f);while(h!==(h=c.cur()/d)&&1!==h&&--i)}return e&&(g=c.start=+g||+d||0,c.unit=f,c.end=e[1]?g+(e[1]+1)*e[2]:+e[2]),c}]};function Sa(){return setTimeout(function(){La=void 0}),La=n.now()}function Ta(a,b){var c,d=0,e={height:a};for(b=b?1:0;4>d;d+=2-b)c=R[d],e["margin"+c]=e["padding"+c]=a;return b&&(e.opacity=e.width=a),e}function Ua(a,b,c){for(var d,e=(Ra[b]||[]).concat(Ra["*"]),f=0,g=e.length;g>f;f++)if(d=e[f].call(c,b,a))return d}function Va(a,b,c){var d,e,f,g,h,i,j,k,l=this,m={},o=a.style,p=a.nodeType&&S(a),q=L.get(a,"fxshow");c.queue||(h=n._queueHooks(a,"fx"),null==h.unqueued&&(h.unqueued=0,i=h.empty.fire,h.empty.fire=function(){h.unqueued||i()}),h.unqueued++,l.always(function(){l.always(function(){h.unqueued--,n.queue(a,"fx").length||h.empty.fire()})})),1===a.nodeType&&("height"in b||"width"in b)&&(c.overflow=[o.overflow,o.overflowX,o.overflowY],j=n.css(a,"display"),k="none"===j?L.get(a,"olddisplay")||ta(a.nodeName):j,"inline"===k&&"none"===n.css(a,"float")&&(o.display="inline-block")),c.overflow&&(o.overflow="hidden",l.always(function(){o.overflow=c.overflow[0],o.overflowX=c.overflow[1],o.overflowY=c.overflow[2]}));for(d in b)if(e=b[d],Na.exec(e)){if(delete b[d],f=f||"toggle"===e,e===(p?"hide":"show")){if("show"!==e||!q||void 0===q[d])continue;p=!0}m[d]=q&&q[d]||n.style(a,d)}else j=void 0;if(n.isEmptyObject(m))"inline"===("none"===j?ta(a.nodeName):j)&&(o.display=j);else{q?"hidden"in q&&(p=q.hidden):q=L.access(a,"fxshow",{}),f&&(q.hidden=!p),p?n(a).show():l.done(function(){n(a).hide()}),l.done(function(){var b;L.remove(a,"fxshow");for(b in m)n.style(a,b,m[b])});for(d in m)g=Ua(p?q[d]:0,d,l),d in q||(q[d]=g.start,p&&(g.end=g.start,g.start="width"===d||"height"===d?1:0))}}function Wa(a,b){var c,d,e,f,g;for(c in a)if(d=n.camelCase(c),e=b[d],f=a[c],n.isArray(f)&&(e=f[1],f=a[c]=f[0]),c!==d&&(a[d]=f,delete a[c]),g=n.cssHooks[d],g&&"expand"in g){f=g.expand(f),delete a[d];for(c in f)c in a||(a[c]=f[c],b[c]=e)}else b[d]=e}function Xa(a,b,c){var d,e,f=0,g=Qa.length,h=n.Deferred().always(function(){delete i.elem}),i=function(){if(e)return!1;for(var b=La||Sa(),c=Math.max(0,j.startTime+j.duration-b),d=c/j.duration||0,f=1-d,g=0,i=j.tweens.length;i>g;g++)j.tweens[g].run(f);return h.notifyWith(a,[j,f,c]),1>f&&i?c:(h.resolveWith(a,[j]),!1)},j=h.promise({elem:a,props:n.extend({},b),opts:n.extend(!0,{specialEasing:{}},c),originalProperties:b,originalOptions:c,startTime:La||Sa(),duration:c.duration,tweens:[],createTween:function(b,c){var d=n.Tween(a,j.opts,b,c,j.opts.specialEasing[b]||j.opts.easing);return j.tweens.push(d),d},stop:function(b){var c=0,d=b?j.tweens.length:0;if(e)return this;for(e=!0;d>c;c++)j.tweens[c].run(1);return b?h.resolveWith(a,[j,b]):h.rejectWith(a,[j,b]),this}}),k=j.props;for(Wa(k,j.opts.specialEasing);g>f;f++)if(d=Qa[f].call(j,a,k,j.opts))return d;return n.map(k,Ua,j),n.isFunction(j.opts.start)&&j.opts.start.call(a,j),n.fx.timer(n.extend(i,{elem:a,anim:j,queue:j.opts.queue})),j.progress(j.opts.progress).done(j.opts.done,j.opts.complete).fail(j.opts.fail).always(j.opts.always)}n.Animation=n.extend(Xa,{tweener:function(a,b){n.isFunction(a)?(b=a,a=["*"]):a=a.split(" ");for(var c,d=0,e=a.length;e>d;d++)c=a[d],Ra[c]=Ra[c]||[],Ra[c].unshift(b)},prefilter:function(a,b){b?Qa.unshift(a):Qa.push(a)}}),n.speed=function(a,b,c){var d=a&&"object"==typeof a?n.extend({},a):{complete:c||!c&&b||n.isFunction(a)&&a,duration:a,easing:c&&b||b&&!n.isFunction(b)&&b};return d.duration=n.fx.off?0:"number"==typeof d.duration?d.duration:d.duration in n.fx.speeds?n.fx.speeds[d.duration]:n.fx.speeds._default,(null==d.queue||d.queue===!0)&&(d.queue="fx"),d.old=d.complete,d.complete=function(){n.isFunction(d.old)&&d.old.call(this),d.queue&&n.dequeue(this,d.queue)},d},n.fn.extend({fadeTo:function(a,b,c,d){return this.filter(S).css("opacity",0).show().end().animate({opacity:b},a,c,d)},animate:function(a,b,c,d){var e=n.isEmptyObject(a),f=n.speed(b,c,d),g=function(){var b=Xa(this,n.extend({},a),f);(e||L.get(this,"finish"))&&b.stop(!0)};return g.finish=g,e||f.queue===!1?this.each(g):this.queue(f.queue,g)},stop:function(a,b,c){var d=function(a){var b=a.stop;delete a.stop,b(c)};return"string"!=typeof a&&(c=b,b=a,a=void 0),b&&a!==!1&&this.queue(a||"fx",[]),this.each(function(){var b=!0,e=null!=a&&a+"queueHooks",f=n.timers,g=L.get(this);if(e)g[e]&&g[e].stop&&d(g[e]);else for(e in g)g[e]&&g[e].stop&&Pa.test(e)&&d(g[e]);for(e=f.length;e--;)f[e].elem!==this||null!=a&&f[e].queue!==a||(f[e].anim.stop(c),b=!1,f.splice(e,1));(b||!c)&&n.dequeue(this,a)})},finish:function(a){return a!==!1&&(a=a||"fx"),this.each(function(){var b,c=L.get(this),d=c[a+"queue"],e=c[a+"queueHooks"],f=n.timers,g=d?d.length:0;for(c.finish=!0,n.queue(this,a,[]),e&&e.stop&&e.stop.call(this,!0),b=f.length;b--;)f[b].elem===this&&f[b].queue===a&&(f[b].anim.stop(!0),f.splice(b,1));for(b=0;g>b;b++)d[b]&&d[b].finish&&d[b].finish.call(this);delete c.finish})}}),n.each(["toggle","show","hide"],function(a,b){var c=n.fn[b];n.fn[b]=function(a,d,e){return null==a||"boolean"==typeof a?c.apply(this,arguments):this.animate(Ta(b,!0),a,d,e)}}),n.each({slideDown:Ta("show"),slideUp:Ta("hide"),slideToggle:Ta("toggle"),fadeIn:{opacity:"show"},fadeOut:{opacity:"hide"},fadeToggle:{opacity:"toggle"}},function(a,b){n.fn[a]=function(a,c,d){return this.animate(b,a,c,d)}}),n.timers=[],n.fx.tick=function(){var a,b=0,c=n.timers;for(La=n.now();b<c.length;b++)a=c[b],a()||c[b]!==a||c.splice(b--,1);c.length||n.fx.stop(),La=void 0},n.fx.timer=function(a){n.timers.push(a),a()?n.fx.start():n.timers.pop()},n.fx.interval=13,n.fx.start=function(){Ma||(Ma=setInterval(n.fx.tick,n.fx.interval))},n.fx.stop=function(){clearInterval(Ma),Ma=null},n.fx.speeds={slow:600,fast:200,_default:400},n.fn.delay=function(a,b){return a=n.fx?n.fx.speeds[a]||a:a,b=b||"fx",this.queue(b,function(b,c){var d=setTimeout(b,a);c.stop=function(){clearTimeout(d)}})},function(){var a=l.createElement("input"),b=l.createElement("select"),c=b.appendChild(l.createElement("option"));a.type="checkbox",k.checkOn=""!==a.value,k.optSelected=c.selected,b.disabled=!0,k.optDisabled=!c.disabled,a=l.createElement("input"),a.value="t",a.type="radio",k.radioValue="t"===a.value}();var Ya,Za,$a=n.expr.attrHandle;n.fn.extend({attr:function(a,b){return J(this,n.attr,a,b,arguments.length>1)},removeAttr:function(a){return this.each(function(){n.removeAttr(this,a)})}}),n.extend({attr:function(a,b,c){var d,e,f=a.nodeType;if(a&&3!==f&&8!==f&&2!==f)return typeof a.getAttribute===U?n.prop(a,b,c):(1===f&&n.isXMLDoc(a)||(b=b.toLowerCase(),d=n.attrHooks[b]||(n.expr.match.bool.test(b)?Za:Ya)),
void 0===c?d&&"get"in d&&null!==(e=d.get(a,b))?e:(e=n.find.attr(a,b),null==e?void 0:e):null!==c?d&&"set"in d&&void 0!==(e=d.set(a,c,b))?e:(a.setAttribute(b,c+""),c):void n.removeAttr(a,b))},removeAttr:function(a,b){var c,d,e=0,f=b&&b.match(E);if(f&&1===a.nodeType)while(c=f[e++])d=n.propFix[c]||c,n.expr.match.bool.test(c)&&(a[d]=!1),a.removeAttribute(c)},attrHooks:{type:{set:function(a,b){if(!k.radioValue&&"radio"===b&&n.nodeName(a,"input")){var c=a.value;return a.setAttribute("type",b),c&&(a.value=c),b}}}}}),Za={set:function(a,b,c){return b===!1?n.removeAttr(a,c):a.setAttribute(c,c),c}},n.each(n.expr.match.bool.source.match(/\w+/g),function(a,b){var c=$a[b]||n.find.attr;$a[b]=function(a,b,d){var e,f;return d||(f=$a[b],$a[b]=e,e=null!=c(a,b,d)?b.toLowerCase():null,$a[b]=f),e}});var _a=/^(?:input|select|textarea|button)$/i;n.fn.extend({prop:function(a,b){return J(this,n.prop,a,b,arguments.length>1)},removeProp:function(a){return this.each(function(){delete this[n.propFix[a]||a]})}}),n.extend({propFix:{"for":"htmlFor","class":"className"},prop:function(a,b,c){var d,e,f,g=a.nodeType;if(a&&3!==g&&8!==g&&2!==g)return f=1!==g||!n.isXMLDoc(a),f&&(b=n.propFix[b]||b,e=n.propHooks[b]),void 0!==c?e&&"set"in e&&void 0!==(d=e.set(a,c,b))?d:a[b]=c:e&&"get"in e&&null!==(d=e.get(a,b))?d:a[b]},propHooks:{tabIndex:{get:function(a){return a.hasAttribute("tabindex")||_a.test(a.nodeName)||a.href?a.tabIndex:-1}}}}),k.optSelected||(n.propHooks.selected={get:function(a){var b=a.parentNode;return b&&b.parentNode&&b.parentNode.selectedIndex,null}}),n.each(["tabIndex","readOnly","maxLength","cellSpacing","cellPadding","rowSpan","colSpan","useMap","frameBorder","contentEditable"],function(){n.propFix[this.toLowerCase()]=this});var ab=/[\t\r\n\f]/g;n.fn.extend({addClass:function(a){var b,c,d,e,f,g,h="string"==typeof a&&a,i=0,j=this.length;if(n.isFunction(a))return this.each(function(b){n(this).addClass(a.call(this,b,this.className))});if(h)for(b=(a||"").match(E)||[];j>i;i++)if(c=this[i],d=1===c.nodeType&&(c.className?(" "+c.className+" ").replace(ab," "):" ")){f=0;while(e=b[f++])d.indexOf(" "+e+" ")<0&&(d+=e+" ");g=n.trim(d),c.className!==g&&(c.className=g)}return this},removeClass:function(a){var b,c,d,e,f,g,h=0===arguments.length||"string"==typeof a&&a,i=0,j=this.length;if(n.isFunction(a))return this.each(function(b){n(this).removeClass(a.call(this,b,this.className))});if(h)for(b=(a||"").match(E)||[];j>i;i++)if(c=this[i],d=1===c.nodeType&&(c.className?(" "+c.className+" ").replace(ab," "):"")){f=0;while(e=b[f++])while(d.indexOf(" "+e+" ")>=0)d=d.replace(" "+e+" "," ");g=a?n.trim(d):"",c.className!==g&&(c.className=g)}return this},toggleClass:function(a,b){var c=typeof a;return"boolean"==typeof b&&"string"===c?b?this.addClass(a):this.removeClass(a):this.each(n.isFunction(a)?function(c){n(this).toggleClass(a.call(this,c,this.className,b),b)}:function(){if("string"===c){var b,d=0,e=n(this),f=a.match(E)||[];while(b=f[d++])e.hasClass(b)?e.removeClass(b):e.addClass(b)}else(c===U||"boolean"===c)&&(this.className&&L.set(this,"__className__",this.className),this.className=this.className||a===!1?"":L.get(this,"__className__")||"")})},hasClass:function(a){for(var b=" "+a+" ",c=0,d=this.length;d>c;c++)if(1===this[c].nodeType&&(" "+this[c].className+" ").replace(ab," ").indexOf(b)>=0)return!0;return!1}});var bb=/\r/g;n.fn.extend({val:function(a){var b,c,d,e=this[0];{if(arguments.length)return d=n.isFunction(a),this.each(function(c){var e;1===this.nodeType&&(e=d?a.call(this,c,n(this).val()):a,null==e?e="":"number"==typeof e?e+="":n.isArray(e)&&(e=n.map(e,function(a){return null==a?"":a+""})),b=n.valHooks[this.type]||n.valHooks[this.nodeName.toLowerCase()],b&&"set"in b&&void 0!==b.set(this,e,"value")||(this.value=e))});if(e)return b=n.valHooks[e.type]||n.valHooks[e.nodeName.toLowerCase()],b&&"get"in b&&void 0!==(c=b.get(e,"value"))?c:(c=e.value,"string"==typeof c?c.replace(bb,""):null==c?"":c)}}}),n.extend({valHooks:{option:{get:function(a){var b=n.find.attr(a,"value");return null!=b?b:n.trim(n.text(a))}},select:{get:function(a){for(var b,c,d=a.options,e=a.selectedIndex,f="select-one"===a.type||0>e,g=f?null:[],h=f?e+1:d.length,i=0>e?h:f?e:0;h>i;i++)if(c=d[i],!(!c.selected&&i!==e||(k.optDisabled?c.disabled:null!==c.getAttribute("disabled"))||c.parentNode.disabled&&n.nodeName(c.parentNode,"optgroup"))){if(b=n(c).val(),f)return b;g.push(b)}return g},set:function(a,b){var c,d,e=a.options,f=n.makeArray(b),g=e.length;while(g--)d=e[g],(d.selected=n.inArray(d.value,f)>=0)&&(c=!0);return c||(a.selectedIndex=-1),f}}}}),n.each(["radio","checkbox"],function(){n.valHooks[this]={set:function(a,b){return n.isArray(b)?a.checked=n.inArray(n(a).val(),b)>=0:void 0}},k.checkOn||(n.valHooks[this].get=function(a){return null===a.getAttribute("value")?"on":a.value})}),n.each("blur focus focusin focusout load resize scroll unload click dblclick mousedown mouseup mousemove mouseover mouseout mouseenter mouseleave change select submit keydown keypress keyup error contextmenu".split(" "),function(a,b){n.fn[b]=function(a,c){return arguments.length>0?this.on(b,null,a,c):this.trigger(b)}}),n.fn.extend({hover:function(a,b){return this.mouseenter(a).mouseleave(b||a)},bind:function(a,b,c){return this.on(a,null,b,c)},unbind:function(a,b){return this.off(a,null,b)},delegate:function(a,b,c,d){return this.on(b,a,c,d)},undelegate:function(a,b,c){return 1===arguments.length?this.off(a,"**"):this.off(b,a||"**",c)}});var cb=n.now(),db=/\?/;n.parseJSON=function(a){return JSON.parse(a+"")},n.parseXML=function(a){var b,c;if(!a||"string"!=typeof a)return null;try{c=new DOMParser,b=c.parseFromString(a,"text/xml")}catch(d){b=void 0}return(!b||b.getElementsByTagName("parsererror").length)&&n.error("Invalid XML: "+a),b};var eb=/#.*$/,fb=/([?&])_=[^&]*/,gb=/^(.*?):[ \t]*([^\r\n]*)$/gm,hb=/^(?:about|app|app-storage|.+-extension|file|res|widget):$/,ib=/^(?:GET|HEAD)$/,jb=/^\/\//,kb=/^([\w.+-]+:)(?:\/\/(?:[^\/?#]*@|)([^\/?#:]*)(?::(\d+)|)|)/,lb={},mb={},nb="*/".concat("*"),ob=a.location.href,pb=kb.exec(ob.toLowerCase())||[];function qb(a){return function(b,c){"string"!=typeof b&&(c=b,b="*");var d,e=0,f=b.toLowerCase().match(E)||[];if(n.isFunction(c))while(d=f[e++])"+"===d[0]?(d=d.slice(1)||"*",(a[d]=a[d]||[]).unshift(c)):(a[d]=a[d]||[]).push(c)}}function rb(a,b,c,d){var e={},f=a===mb;function g(h){var i;return e[h]=!0,n.each(a[h]||[],function(a,h){var j=h(b,c,d);return"string"!=typeof j||f||e[j]?f?!(i=j):void 0:(b.dataTypes.unshift(j),g(j),!1)}),i}return g(b.dataTypes[0])||!e["*"]&&g("*")}function sb(a,b){var c,d,e=n.ajaxSettings.flatOptions||{};for(c in b)void 0!==b[c]&&((e[c]?a:d||(d={}))[c]=b[c]);return d&&n.extend(!0,a,d),a}function tb(a,b,c){var d,e,f,g,h=a.contents,i=a.dataTypes;while("*"===i[0])i.shift(),void 0===d&&(d=a.mimeType||b.getResponseHeader("Content-Type"));if(d)for(e in h)if(h[e]&&h[e].test(d)){i.unshift(e);break}if(i[0]in c)f=i[0];else{for(e in c){if(!i[0]||a.converters[e+" "+i[0]]){f=e;break}g||(g=e)}f=f||g}return f?(f!==i[0]&&i.unshift(f),c[f]):void 0}function ub(a,b,c,d){var e,f,g,h,i,j={},k=a.dataTypes.slice();if(k[1])for(g in a.converters)j[g.toLowerCase()]=a.converters[g];f=k.shift();while(f)if(a.responseFields[f]&&(c[a.responseFields[f]]=b),!i&&d&&a.dataFilter&&(b=a.dataFilter(b,a.dataType)),i=f,f=k.shift())if("*"===f)f=i;else if("*"!==i&&i!==f){if(g=j[i+" "+f]||j["* "+f],!g)for(e in j)if(h=e.split(" "),h[1]===f&&(g=j[i+" "+h[0]]||j["* "+h[0]])){g===!0?g=j[e]:j[e]!==!0&&(f=h[0],k.unshift(h[1]));break}if(g!==!0)if(g&&a["throws"])b=g(b);else try{b=g(b)}catch(l){return{state:"parsererror",error:g?l:"No conversion from "+i+" to "+f}}}return{state:"success",data:b}}n.extend({active:0,lastModified:{},etag:{},ajaxSettings:{url:ob,type:"GET",isLocal:hb.test(pb[1]),global:!0,processData:!0,async:!0,contentType:"application/x-www-form-urlencoded; charset=UTF-8",accepts:{"*":nb,text:"text/plain",html:"text/html",xml:"application/xml, text/xml",json:"application/json, text/javascript"},contents:{xml:/xml/,html:/html/,json:/json/},responseFields:{xml:"responseXML",text:"responseText",json:"responseJSON"},converters:{"* text":String,"text html":!0,"text json":n.parseJSON,"text xml":n.parseXML},flatOptions:{url:!0,context:!0}},ajaxSetup:function(a,b){return b?sb(sb(a,n.ajaxSettings),b):sb(n.ajaxSettings,a)},ajaxPrefilter:qb(lb),ajaxTransport:qb(mb),ajax:function(a,b){"object"==typeof a&&(b=a,a=void 0),b=b||{};var c,d,e,f,g,h,i,j,k=n.ajaxSetup({},b),l=k.context||k,m=k.context&&(l.nodeType||l.jquery)?n(l):n.event,o=n.Deferred(),p=n.Callbacks("once memory"),q=k.statusCode||{},r={},s={},t=0,u="canceled",v={readyState:0,getResponseHeader:function(a){var b;if(2===t){if(!f){f={};while(b=gb.exec(e))f[b[1].toLowerCase()]=b[2]}b=f[a.toLowerCase()]}return null==b?null:b},getAllResponseHeaders:function(){return 2===t?e:null},setRequestHeader:function(a,b){var c=a.toLowerCase();return t||(a=s[c]=s[c]||a,r[a]=b),this},overrideMimeType:function(a){return t||(k.mimeType=a),this},statusCode:function(a){var b;if(a)if(2>t)for(b in a)q[b]=[q[b],a[b]];else v.always(a[v.status]);return this},abort:function(a){var b=a||u;return c&&c.abort(b),x(0,b),this}};if(o.promise(v).complete=p.add,v.success=v.done,v.error=v.fail,k.url=((a||k.url||ob)+"").replace(eb,"").replace(jb,pb[1]+"//"),k.type=b.method||b.type||k.method||k.type,k.dataTypes=n.trim(k.dataType||"*").toLowerCase().match(E)||[""],null==k.crossDomain&&(h=kb.exec(k.url.toLowerCase()),k.crossDomain=!(!h||h[1]===pb[1]&&h[2]===pb[2]&&(h[3]||("http:"===h[1]?"80":"443"))===(pb[3]||("http:"===pb[1]?"80":"443")))),k.data&&k.processData&&"string"!=typeof k.data&&(k.data=n.param(k.data,k.traditional)),rb(lb,k,b,v),2===t)return v;i=n.event&&k.global,i&&0===n.active++&&n.event.trigger("ajaxStart"),k.type=k.type.toUpperCase(),k.hasContent=!ib.test(k.type),d=k.url,k.hasContent||(k.data&&(d=k.url+=(db.test(d)?"&":"?")+k.data,delete k.data),k.cache===!1&&(k.url=fb.test(d)?d.replace(fb,"$1_="+cb++):d+(db.test(d)?"&":"?")+"_="+cb++)),k.ifModified&&(n.lastModified[d]&&v.setRequestHeader("If-Modified-Since",n.lastModified[d]),n.etag[d]&&v.setRequestHeader("If-None-Match",n.etag[d])),(k.data&&k.hasContent&&k.contentType!==!1||b.contentType)&&v.setRequestHeader("Content-Type",k.contentType),v.setRequestHeader("Accept",k.dataTypes[0]&&k.accepts[k.dataTypes[0]]?k.accepts[k.dataTypes[0]]+("*"!==k.dataTypes[0]?", "+nb+"; q=0.01":""):k.accepts["*"]);for(j in k.headers)v.setRequestHeader(j,k.headers[j]);if(k.beforeSend&&(k.beforeSend.call(l,v,k)===!1||2===t))return v.abort();u="abort";for(j in{success:1,error:1,complete:1})v[j](k[j]);if(c=rb(mb,k,b,v)){v.readyState=1,i&&m.trigger("ajaxSend",[v,k]),k.async&&k.timeout>0&&(g=setTimeout(function(){v.abort("timeout")},k.timeout));try{t=1,c.send(r,x)}catch(w){if(!(2>t))throw w;x(-1,w)}}else x(-1,"No Transport");function x(a,b,f,h){var j,r,s,u,w,x=b;2!==t&&(t=2,g&&clearTimeout(g),c=void 0,e=h||"",v.readyState=a>0?4:0,j=a>=200&&300>a||304===a,f&&(u=tb(k,v,f)),u=ub(k,u,v,j),j?(k.ifModified&&(w=v.getResponseHeader("Last-Modified"),w&&(n.lastModified[d]=w),w=v.getResponseHeader("etag"),w&&(n.etag[d]=w)),204===a||"HEAD"===k.type?x="nocontent":304===a?x="notmodified":(x=u.state,r=u.data,s=u.error,j=!s)):(s=x,(a||!x)&&(x="error",0>a&&(a=0))),v.status=a,v.statusText=(b||x)+"",j?o.resolveWith(l,[r,x,v]):o.rejectWith(l,[v,x,s]),v.statusCode(q),q=void 0,i&&m.trigger(j?"ajaxSuccess":"ajaxError",[v,k,j?r:s]),p.fireWith(l,[v,x]),i&&(m.trigger("ajaxComplete",[v,k]),--n.active||n.event.trigger("ajaxStop")))}return v},getJSON:function(a,b,c){return n.get(a,b,c,"json")},getScript:function(a,b){return n.get(a,void 0,b,"script")}}),n.each(["get","post"],function(a,b){n[b]=function(a,c,d,e){return n.isFunction(c)&&(e=e||d,d=c,c=void 0),n.ajax({url:a,type:b,dataType:e,data:c,success:d})}}),n._evalUrl=function(a){return n.ajax({url:a,type:"GET",dataType:"script",async:!1,global:!1,"throws":!0})},n.fn.extend({wrapAll:function(a){var b;return n.isFunction(a)?this.each(function(b){n(this).wrapAll(a.call(this,b))}):(this[0]&&(b=n(a,this[0].ownerDocument).eq(0).clone(!0),this[0].parentNode&&b.insertBefore(this[0]),b.map(function(){var a=this;while(a.firstElementChild)a=a.firstElementChild;return a}).append(this)),this)},wrapInner:function(a){return this.each(n.isFunction(a)?function(b){n(this).wrapInner(a.call(this,b))}:function(){var b=n(this),c=b.contents();c.length?c.wrapAll(a):b.append(a)})},wrap:function(a){var b=n.isFunction(a);return this.each(function(c){n(this).wrapAll(b?a.call(this,c):a)})},unwrap:function(){return this.parent().each(function(){n.nodeName(this,"body")||n(this).replaceWith(this.childNodes)}).end()}}),n.expr.filters.hidden=function(a){return a.offsetWidth<=0&&a.offsetHeight<=0},n.expr.filters.visible=function(a){return!n.expr.filters.hidden(a)};var vb=/%20/g,wb=/\[\]$/,xb=/\r?\n/g,yb=/^(?:submit|button|image|reset|file)$/i,zb=/^(?:input|select|textarea|keygen)/i;function Ab(a,b,c,d){var e;if(n.isArray(b))n.each(b,function(b,e){c||wb.test(a)?d(a,e):Ab(a+"["+("object"==typeof e?b:"")+"]",e,c,d)});else if(c||"object"!==n.type(b))d(a,b);else for(e in b)Ab(a+"["+e+"]",b[e],c,d)}n.param=function(a,b){var c,d=[],e=function(a,b){b=n.isFunction(b)?b():null==b?"":b,d[d.length]=encodeURIComponent(a)+"="+encodeURIComponent(b)};if(void 0===b&&(b=n.ajaxSettings&&n.ajaxSettings.traditional),n.isArray(a)||a.jquery&&!n.isPlainObject(a))n.each(a,function(){e(this.name,this.value)});else for(c in a)Ab(c,a[c],b,e);return d.join("&").replace(vb,"+")},n.fn.extend({serialize:function(){return n.param(this.serializeArray())},serializeArray:function(){return this.map(function(){var a=n.prop(this,"elements");return a?n.makeArray(a):this}).filter(function(){var a=this.type;return this.name&&!n(this).is(":disabled")&&zb.test(this.nodeName)&&!yb.test(a)&&(this.checked||!T.test(a))}).map(function(a,b){var c=n(this).val();return null==c?null:n.isArray(c)?n.map(c,function(a){return{name:b.name,value:a.replace(xb,"\r\n")}}):{name:b.name,value:c.replace(xb,"\r\n")}}).get()}}),n.ajaxSettings.xhr=function(){try{return new XMLHttpRequest}catch(a){}};var Bb=0,Cb={},Db={0:200,1223:204},Eb=n.ajaxSettings.xhr();a.attachEvent&&a.attachEvent("onunload",function(){for(var a in Cb)Cb[a]()}),k.cors=!!Eb&&"withCredentials"in Eb,k.ajax=Eb=!!Eb,n.ajaxTransport(function(a){var b;return k.cors||Eb&&!a.crossDomain?{send:function(c,d){var e,f=a.xhr(),g=++Bb;if(f.open(a.type,a.url,a.async,a.username,a.password),a.xhrFields)for(e in a.xhrFields)f[e]=a.xhrFields[e];a.mimeType&&f.overrideMimeType&&f.overrideMimeType(a.mimeType),a.crossDomain||c["X-Requested-With"]||(c["X-Requested-With"]="XMLHttpRequest");for(e in c)f.setRequestHeader(e,c[e]);b=function(a){return function(){b&&(delete Cb[g],b=f.onload=f.onerror=null,"abort"===a?f.abort():"error"===a?d(f.status,f.statusText):d(Db[f.status]||f.status,f.statusText,"string"==typeof f.responseText?{text:f.responseText}:void 0,f.getAllResponseHeaders()))}},f.onload=b(),f.onerror=b("error"),b=Cb[g]=b("abort");try{f.send(a.hasContent&&a.data||null)}catch(h){if(b)throw h}},abort:function(){b&&b()}}:void 0}),n.ajaxSetup({accepts:{script:"text/javascript, application/javascript, application/ecmascript, application/x-ecmascript"},contents:{script:/(?:java|ecma)script/},converters:{"text script":function(a){return n.globalEval(a),a}}}),n.ajaxPrefilter("script",function(a){void 0===a.cache&&(a.cache=!1),a.crossDomain&&(a.type="GET")}),n.ajaxTransport("script",function(a){if(a.crossDomain){var b,c;return{send:function(d,e){b=n("<script>").prop({async:!0,charset:a.scriptCharset,src:a.url}).on("load error",c=function(a){b.remove(),c=null,a&&e("error"===a.type?404:200,a.type)}),l.head.appendChild(b[0])},abort:function(){c&&c()}}}});var Fb=[],Gb=/(=)\?(?=&|$)|\?\?/;n.ajaxSetup({jsonp:"callback",jsonpCallback:function(){var a=Fb.pop()||n.expando+"_"+cb++;return this[a]=!0,a}}),n.ajaxPrefilter("json jsonp",function(b,c,d){var e,f,g,h=b.jsonp!==!1&&(Gb.test(b.url)?"url":"string"==typeof b.data&&!(b.contentType||"").indexOf("application/x-www-form-urlencoded")&&Gb.test(b.data)&&"data");return h||"jsonp"===b.dataTypes[0]?(e=b.jsonpCallback=n.isFunction(b.jsonpCallback)?b.jsonpCallback():b.jsonpCallback,h?b[h]=b[h].replace(Gb,"$1"+e):b.jsonp!==!1&&(b.url+=(db.test(b.url)?"&":"?")+b.jsonp+"="+e),b.converters["script json"]=function(){return g||n.error(e+" was not called"),g[0]},b.dataTypes[0]="json",f=a[e],a[e]=function(){g=arguments},d.always(function(){a[e]=f,b[e]&&(b.jsonpCallback=c.jsonpCallback,Fb.push(e)),g&&n.isFunction(f)&&f(g[0]),g=f=void 0}),"script"):void 0}),n.parseHTML=function(a,b,c){if(!a||"string"!=typeof a)return null;"boolean"==typeof b&&(c=b,b=!1),b=b||l;var d=v.exec(a),e=!c&&[];return d?[b.createElement(d[1])]:(d=n.buildFragment([a],b,e),e&&e.length&&n(e).remove(),n.merge([],d.childNodes))};var Hb=n.fn.load;n.fn.load=function(a,b,c){if("string"!=typeof a&&Hb)return Hb.apply(this,arguments);var d,e,f,g=this,h=a.indexOf(" ");return h>=0&&(d=n.trim(a.slice(h)),a=a.slice(0,h)),n.isFunction(b)?(c=b,b=void 0):b&&"object"==typeof b&&(e="POST"),g.length>0&&n.ajax({url:a,type:e,dataType:"html",data:b}).done(function(a){f=arguments,g.html(d?n("<div>").append(n.parseHTML(a)).find(d):a)}).complete(c&&function(a,b){g.each(c,f||[a.responseText,b,a])}),this},n.each(["ajaxStart","ajaxStop","ajaxComplete","ajaxError","ajaxSuccess","ajaxSend"],function(a,b){n.fn[b]=function(a){return this.on(b,a)}}),n.expr.filters.animated=function(a){return n.grep(n.timers,function(b){return a===b.elem}).length};var Ib=a.document.documentElement;function Jb(a){return n.isWindow(a)?a:9===a.nodeType&&a.defaultView}n.offset={setOffset:function(a,b,c){var d,e,f,g,h,i,j,k=n.css(a,"position"),l=n(a),m={};"static"===k&&(a.style.position="relative"),h=l.offset(),f=n.css(a,"top"),i=n.css(a,"left"),j=("absolute"===k||"fixed"===k)&&(f+i).indexOf("auto")>-1,j?(d=l.position(),g=d.top,e=d.left):(g=parseFloat(f)||0,e=parseFloat(i)||0),n.isFunction(b)&&(b=b.call(a,c,h)),null!=b.top&&(m.top=b.top-h.top+g),null!=b.left&&(m.left=b.left-h.left+e),"using"in b?b.using.call(a,m):l.css(m)}},n.fn.extend({offset:function(a){if(arguments.length)return void 0===a?this:this.each(function(b){n.offset.setOffset(this,a,b)});var b,c,d=this[0],e={top:0,left:0},f=d&&d.ownerDocument;if(f)return b=f.documentElement,n.contains(b,d)?(typeof d.getBoundingClientRect!==U&&(e=d.getBoundingClientRect()),c=Jb(f),{top:e.top+c.pageYOffset-b.clientTop,left:e.left+c.pageXOffset-b.clientLeft}):e},position:function(){if(this[0]){var a,b,c=this[0],d={top:0,left:0};return"fixed"===n.css(c,"position")?b=c.getBoundingClientRect():(a=this.offsetParent(),b=this.offset(),n.nodeName(a[0],"html")||(d=a.offset()),d.top+=n.css(a[0],"borderTopWidth",!0),d.left+=n.css(a[0],"borderLeftWidth",!0)),{top:b.top-d.top-n.css(c,"marginTop",!0),left:b.left-d.left-n.css(c,"marginLeft",!0)}}},offsetParent:function(){return this.map(function(){var a=this.offsetParent||Ib;while(a&&!n.nodeName(a,"html")&&"static"===n.css(a,"position"))a=a.offsetParent;return a||Ib})}}),n.each({scrollLeft:"pageXOffset",scrollTop:"pageYOffset"},function(b,c){var d="pageYOffset"===c;n.fn[b]=function(e){return J(this,function(b,e,f){var g=Jb(b);return void 0===f?g?g[c]:b[e]:void(g?g.scrollTo(d?a.pageXOffset:f,d?f:a.pageYOffset):b[e]=f)},b,e,arguments.length,null)}}),n.each(["top","left"],function(a,b){n.cssHooks[b]=ya(k.pixelPosition,function(a,c){return c?(c=xa(a,b),va.test(c)?n(a).position()[b]+"px":c):void 0})}),n.each({Height:"height",Width:"width"},function(a,b){n.each({padding:"inner"+a,content:b,"":"outer"+a},function(c,d){n.fn[d]=function(d,e){var f=arguments.length&&(c||"boolean"!=typeof d),g=c||(d===!0||e===!0?"margin":"border");return J(this,function(b,c,d){var e;return n.isWindow(b)?b.document.documentElement["client"+a]:9===b.nodeType?(e=b.documentElement,Math.max(b.body["scroll"+a],e["scroll"+a],b.body["offset"+a],e["offset"+a],e["client"+a])):void 0===d?n.css(b,c,g):n.style(b,c,d,g)},b,f?d:void 0,f,null)}})}),n.fn.size=function(){return this.length},n.fn.andSelf=n.fn.addBack,"function"==typeof define&&define.amd&&define("jquery",[],function(){return n});var Kb=a.jQuery,Lb=a.$;return n.noConflict=function(b){return a.$===n&&(a.$=Lb),b&&a.jQuery===n&&(a.jQuery=Kb),n},typeof b===U&&(a.jQuery=a.$=n),n});
//# sourceMappingURL=jquery.min.map
/* Copyright (C) 1991-2017 Free Software Foundation, Inc.
   This file is part of the GNU C Library.

   The GNU C Library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2.1 of the License, or (at your option) any later version.

   The GNU C Library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public
   License along with the GNU C Library; if not, see
   <http://www.gnu.org/licenses/>.  */
/* This header is separate from features.h so that the compiler can
   include it implicitly at the start of every compilation.  It must
   not itself include <features.h> or any other header that includes
   <features.h> because the implicit include comes before any feature
   test macros that may be defined in a source file before it first
   explicitly includes a system header.  GCC knows the name of this
   header in order to preinclude it.  */
/* glibc's intent is to support the IEC 559 math functionality, real
   and complex.  If the GCC (4.9 and later) predefined macros
   specifying compiler intent are available, use them to determine
   whether the overall intent is to support these features; otherwise,
   presume an older compiler has intent to support these features and
   define these macros by default.  */
/* wchar_t uses Unicode 8.0.0.  Version 8.0 of the Unicode Standard is
   synchronized with ISO/IEC 10646:2014, plus Amendment 1 (published
   2015-05-15).  */
/* We do not support C11 <threads.h>.  */
 /*
 * # Semantic UI - 2.4.1
 * https://github.com/Semantic-Org/Semantic-UI
 * http://www.semantic-ui.com/
 *
 * Copyright 2014 Contributors
 * Released under the MIT license
 * http://opensource.org/licenses/MIT
 *
 */
!function(p,h,v,b){p.site=p.fn.site=function(e){var s,l,i=(new Date).getTime(),o=[],t=e,n="string"==typeof t,c=[].slice.call(arguments,1),u=p.isPlainObject(e)?p.extend(!0,{},p.site.settings,e):p.extend({},p.site.settings),a=u.namespace,d=u.error,r="module-"+a,f=p(v),m=this,g=f.data(r);return s={initialize:function(){s.instantiate()},instantiate:function(){s.verbose("Storing instance of site",s),g=s,f.data(r,s)},normalize:function(){s.fix.console(),s.fix.requestAnimationFrame()},fix:{console:function(){s.debug("Normalizing window.console"),console!==b&&console.log!==b||(s.verbose("Console not available, normalizing events"),s.disable.console()),void 0!==console.group&&void 0!==console.groupEnd&&void 0!==console.groupCollapsed||(s.verbose("Console group not available, normalizing events"),h.console.group=function(){},h.console.groupEnd=function(){},h.console.groupCollapsed=function(){}),void 0===console.markTimeline&&(s.verbose("Mark timeline not available, normalizing events"),h.console.markTimeline=function(){})},consoleClear:function(){s.debug("Disabling programmatic console clearing"),h.console.clear=function(){}},requestAnimationFrame:function(){s.debug("Normalizing requestAnimationFrame"),h.requestAnimationFrame===b&&(s.debug("RequestAnimationFrame not available, normalizing event"),h.requestAnimationFrame=h.requestAnimationFrame||h.mozRequestAnimationFrame||h.webkitRequestAnimationFrame||h.msRequestAnimationFrame||function(e){setTimeout(e,0)})}},moduleExists:function(e){return p.fn[e]!==b&&p.fn[e].settings!==b},enabled:{modules:function(e){var n=[];return e=e||u.modules,p.each(e,function(e,t){s.moduleExists(t)&&n.push(t)}),n}},disabled:{modules:function(e){var n=[];return e=e||u.modules,p.each(e,function(e,t){s.moduleExists(t)||n.push(t)}),n}},change:{setting:function(o,a,e,r){e="string"==typeof e?"all"===e?u.modules:[e]:e||u.modules,r=r===b||r,p.each(e,function(e,t){var n,i=!s.moduleExists(t)||(p.fn[t].settings.namespace||!1);s.moduleExists(t)&&(s.verbose("Changing default setting",o,a,t),p.fn[t].settings[o]=a,r&&i&&0<(n=p(":data(module-"+i+")")).length&&(s.verbose("Modifying existing settings",n),n[t]("setting",o,a)))})},settings:function(i,e,o){e="string"==typeof e?[e]:e||u.modules,o=o===b||o,p.each(e,function(e,t){var n;s.moduleExists(t)&&(s.verbose("Changing default setting",i,t),p.extend(!0,p.fn[t].settings,i),o&&a&&0<(n=p(":data(module-"+a+")")).length&&(s.verbose("Modifying existing settings",n),n[t]("setting",i)))})}},enable:{console:function(){s.console(!0)},debug:function(e,t){e=e||u.modules,s.debug("Enabling debug for modules",e),s.change.setting("debug",!0,e,t)},verbose:function(e,t){e=e||u.modules,s.debug("Enabling verbose debug for modules",e),s.change.setting("verbose",!0,e,t)}},disable:{console:function(){s.console(!1)},debug:function(e,t){e=e||u.modules,s.debug("Disabling debug for modules",e),s.change.setting("debug",!1,e,t)},verbose:function(e,t){e=e||u.modules,s.debug("Disabling verbose debug for modules",e),s.change.setting("verbose",!1,e,t)}},console:function(e){if(e){if(g.cache.console===b)return void s.error(d.console);s.debug("Restoring console function"),h.console=g.cache.console}else s.debug("Disabling console function"),g.cache.console=h.console,h.console={clear:function(){},error:function(){},group:function(){},groupCollapsed:function(){},groupEnd:function(){},info:function(){},log:function(){},markTimeline:function(){},warn:function(){}}},destroy:function(){s.verbose("Destroying previous site for",f),f.removeData(r)},cache:{},setting:function(e,t){if(p.isPlainObject(e))p.extend(!0,u,e);else{if(t===b)return u[e];u[e]=t}},internal:function(e,t){if(p.isPlainObject(e))p.extend(!0,s,e);else{if(t===b)return s[e];s[e]=t}},debug:function(){u.debug&&(u.performance?s.performance.log(arguments):(s.debug=Function.prototype.bind.call(console.info,console,u.name+":"),s.debug.apply(console,arguments)))},verbose:function(){u.verbose&&u.debug&&(u.performance?s.performance.log(arguments):(s.verbose=Function.prototype.bind.call(console.info,console,u.name+":"),s.verbose.apply(console,arguments)))},error:function(){s.error=Function.prototype.bind.call(console.error,console,u.name+":"),s.error.apply(console,arguments)},performance:{log:function(e){var t,n;u.performance&&(n=(t=(new Date).getTime())-(i||t),i=t,o.push({Element:m,Name:e[0],Arguments:[].slice.call(e,1)||"","Execution Time":n})),clearTimeout(s.performance.timer),s.performance.timer=setTimeout(s.performance.display,500)},display:function(){var e=u.name+":",n=0;i=!1,clearTimeout(s.performance.timer),p.each(o,function(e,t){n+=t["Execution Time"]}),e+=" "+n+"ms",(console.group!==b||console.table!==b)&&0<o.length&&(console.groupCollapsed(e),console.table?console.table(o):p.each(o,function(e,t){console.log(t.Name+": "+t["Execution Time"]+"ms")}),console.groupEnd()),o=[]}},invoke:function(i,e,t){var o,a,n,r=g;return e=e||c,t=m||t,"string"==typeof i&&r!==b&&(i=i.split(/[\. ]/),o=i.length-1,p.each(i,function(e,t){var n=e!=o?t+i[e+1].charAt(0).toUpperCase()+i[e+1].slice(1):i;if(p.isPlainObject(r[n])&&e!=o)r=r[n];else{if(r[n]!==b)return a=r[n],!1;if(!p.isPlainObject(r[t])||e==o)return r[t]!==b?a=r[t]:s.error(d.method,i),!1;r=r[t]}})),p.isFunction(a)?n=a.apply(t,e):a!==b&&(n=a),p.isArray(l)?l.push(n):l!==b?l=[l,n]:n!==b&&(l=n),a}},n?(g===b&&s.initialize(),s.invoke(t)):(g!==b&&s.destroy(),s.initialize()),l!==b?l:this},p.site.settings={name:"Site",namespace:"site",error:{console:"Console cannot be restored, most likely it was overwritten outside of module",method:"The method you called is not defined."},debug:!1,verbose:!1,performance:!0,modules:["accordion","api","checkbox","dimmer","dropdown","embed","form","modal","nag","popup","rating","shape","sidebar","state","sticky","tab","transition","visit","visibility"],siteNamespace:"site",namespaceStub:{cache:{},config:{},sections:{},section:{},utilities:{}}},p.extend(p.expr[":"],{data:p.expr.createPseudo?p.expr.createPseudo(function(t){return function(e){return!!p.data(e,t)}}):function(e,t,n){return!!p.data(e,n[3])}})}(jQuery,window,document),function(F,e,O,D){"use strict";e=void 0!==e&&e.Math==Math?e:"undefined"!=typeof self&&self.Math==Math?self:Function("return this")(),F.fn.form=function(x){var C,w=F(this),S=w.selector||"",k=(new Date).getTime(),T=[],A=x,R=arguments[1],P="string"==typeof A,E=[].slice.call(arguments,1);return w.each(function(){var n,l,t,e,d,c,u,f,m,i,s,o,a,g,p,h,r=F(this),v=this,b=[],y=!1;(h={initialize:function(){h.get.settings(),P?(p===D&&h.instantiate(),h.invoke(A)):(p!==D&&p.invoke("destroy"),h.verbose("Initializing form validation",r,d),h.bindEvents(),h.set.defaults(),h.instantiate())},instantiate:function(){h.verbose("Storing instance of module",h),p=h,r.data(a,h)},destroy:function(){h.verbose("Destroying previous module",p),h.removeEvents(),r.removeData(a)},refresh:function(){h.verbose("Refreshing selector cache"),n=r.find(f.field),l=r.find(f.group),t=r.find(f.message),r.find(f.prompt),e=r.find(f.submit),r.find(f.clear),r.find(f.reset)},submit:function(){h.verbose("Submitting form",r),r.submit()},attachEvents:function(e,t){t=t||"submit",F(e).on("click"+g,function(e){h[t](),e.preventDefault()})},bindEvents:function(){h.verbose("Attaching form events"),r.on("submit"+g,h.validate.form).on("blur"+g,f.field,h.event.field.blur).on("click"+g,f.submit,h.submit).on("click"+g,f.reset,h.reset).on("click"+g,f.clear,h.clear),d.keyboardShortcuts&&r.on("keydown"+g,f.field,h.event.field.keydown),n.each(function(){var e=F(this),t=e.prop("type"),n=h.get.changeEvent(t,e);F(this).on(n+g,h.event.field.change)})},clear:function(){n.each(function(){var e=F(this),t=e.parent(),n=e.closest(l),i=n.find(f.prompt),o=e.data(u.defaultValue)||"",a=t.is(f.uiCheckbox),r=t.is(f.uiDropdown);n.hasClass(m.error)&&(h.verbose("Resetting error on field",n),n.removeClass(m.error),i.remove()),r?(h.verbose("Resetting dropdown value",t,o),t.dropdown("clear")):a?e.prop("checked",!1):(h.verbose("Resetting field value",e,o),e.val(""))})},reset:function(){n.each(function(){var e=F(this),t=e.parent(),n=e.closest(l),i=n.find(f.prompt),o=e.data(u.defaultValue),a=t.is(f.uiCheckbox),r=t.is(f.uiDropdown),s=n.hasClass(m.error);o!==D&&(s&&(h.verbose("Resetting error on field",n),n.removeClass(m.error),i.remove()),r?(h.verbose("Resetting dropdown value",t,o),t.dropdown("restore defaults")):a?(h.verbose("Resetting checkbox value",t,o),e.prop("checked",o)):(h.verbose("Resetting field value",e,o),e.val(o)))})},determine:{isValid:function(){var n=!0;return F.each(c,function(e,t){h.validate.field(t,e,!0)||(n=!1)}),n}},is:{bracketedRule:function(e){return e.type&&e.type.match(d.regExp.bracket)},shorthandFields:function(e){var t=e[Object.keys(e)[0]];return h.is.shorthandRules(t)},shorthandRules:function(e){return"string"==typeof e||F.isArray(e)},empty:function(e){return!e||0===e.length||(e.is('input[type="checkbox"]')?!e.is(":checked"):h.is.blank(e))},blank:function(e){return""===F.trim(e.val())},valid:function(e){var n=!0;return e?(h.verbose("Checking if field is valid",e),h.validate.field(c[e],e,!1)):(h.verbose("Checking if form is valid"),F.each(c,function(e,t){h.is.valid(e)||(n=!1)}),n)}},removeEvents:function(){r.off(g),n.off(g),e.off(g),n.off(g)},event:{field:{keydown:function(e){var t=F(this),n=e.which,i=t.is(f.input),o=t.is(f.checkbox),a=0<t.closest(f.uiDropdown).length,r=13;n==27&&(h.verbose("Escape key pressed blurring field"),t.blur()),e.ctrlKey||n!=r||!i||a||o||(y||(t.one("keyup"+g,h.event.field.keyup),h.submit(),h.debug("Enter pressed on input submitting form")),y=!0)},keyup:function(){y=!1},blur:function(e){var t=F(this),n=t.closest(l),i=h.get.validation(t);n.hasClass(m.error)?(h.debug("Revalidating field",t,i),i&&h.validate.field(i)):"blur"==d.on&&i&&h.validate.field(i)},change:function(e){var t=F(this),n=t.closest(l),i=h.get.validation(t);i&&("change"==d.on||n.hasClass(m.error)&&d.revalidate)&&(clearTimeout(h.timer),h.timer=setTimeout(function(){h.debug("Revalidating field",t,h.get.validation(t)),h.validate.field(i)},d.delay))}}},get:{ancillaryValue:function(e){return!(!e.type||!e.value&&!h.is.bracketedRule(e))&&(e.value!==D?e.value:e.type.match(d.regExp.bracket)[1]+"")},ruleName:function(e){return h.is.bracketedRule(e)?e.type.replace(e.type.match(d.regExp.bracket)[0],""):e.type},changeEvent:function(e,t){return"checkbox"==e||"radio"==e||"hidden"==e||t.is("select")?"change":h.get.inputEvent()},inputEvent:function(){return O.createElement("input").oninput!==D?"input":O.createElement("input").onpropertychange!==D?"propertychange":"keyup"},fieldsFromShorthand:function(e){var i={};return F.each(e,function(n,e){"string"==typeof e&&(e=[e]),i[n]={rules:[]},F.each(e,function(e,t){i[n].rules.push({type:t})})}),i},prompt:function(e,t){var n,i,o=h.get.ruleName(e),a=h.get.ancillaryValue(e),r=h.get.field(t.identifier),s=r.val(),l=F.isFunction(e.prompt)?e.prompt(s):e.prompt||d.prompt[o]||d.text.unspecifiedRule,c=-1!==l.search("{value}"),u=-1!==l.search("{name}");return c&&(l=l.replace("{value}",r.val())),u&&(i=1==(n=r.closest(f.group).find("label").eq(0)).length?n.text():r.prop("placeholder")||d.text.unspecifiedField,l=l.replace("{name}",i)),l=(l=l.replace("{identifier}",t.identifier)).replace("{ruleValue}",a),e.prompt||h.verbose("Using default validation prompt for type",l,o),l},settings:function(){if(F.isPlainObject(x)){var e=Object.keys(x);0<e.length&&(x[e[0]].identifier!==D&&x[e[0]].rules!==D)?(d=F.extend(!0,{},F.fn.form.settings,R),c=F.extend({},F.fn.form.settings.defaults,x),h.error(d.error.oldSyntax,v),h.verbose("Extending settings from legacy parameters",c,d)):(x.fields&&h.is.shorthandFields(x.fields)&&(x.fields=h.get.fieldsFromShorthand(x.fields)),d=F.extend(!0,{},F.fn.form.settings,x),c=F.extend({},F.fn.form.settings.defaults,d.fields),h.verbose("Extending settings",c,d))}else d=F.fn.form.settings,c=F.fn.form.settings.defaults,h.verbose("Using default form validation",c,d);o=d.namespace,u=d.metadata,f=d.selector,m=d.className,i=d.regExp,s=d.error,a="module-"+o,g="."+o,p=r.data(a),h.refresh()},field:function(e){return h.verbose("Finding field with identifier",e),e=h.escape.string(e),0<n.filter("#"+e).length?n.filter("#"+e):0<n.filter('[name="'+e+'"]').length?n.filter('[name="'+e+'"]'):0<n.filter('[name="'+e+'[]"]').length?n.filter('[name="'+e+'[]"]'):0<n.filter("[data-"+u.validate+'="'+e+'"]').length?n.filter("[data-"+u.validate+'="'+e+'"]'):F("<input/>")},fields:function(e){var n=F();return F.each(e,function(e,t){n=n.add(h.get.field(t))}),n},validation:function(n){var i,o;return!!c&&(F.each(c,function(e,t){o=t.identifier||e,h.get.field(o)[0]==n[0]&&(t.identifier=o,i=t)}),i||!1)},value:function(e){var t=[];return t.push(e),h.get.values.call(v,t)[e]},values:function(e){var t=F.isArray(e)?h.get.fields(e):n,c={};return t.each(function(e,t){var n=F(t),i=(n.prop("type"),n.prop("name")),o=n.val(),a=n.is(f.checkbox),r=n.is(f.radio),s=-1!==i.indexOf("[]"),l=!!a&&n.is(":checked");i&&(s?(i=i.replace("[]",""),c[i]||(c[i]=[]),a?l?c[i].push(o||!0):c[i].push(!1):c[i].push(o)):r?c[i]!==D&&0!=c[i]||(c[i]=!!l&&(o||!0)):c[i]=a?!!l&&(o||!0):o)}),c}},has:{field:function(e){return h.verbose("Checking for existence of a field with identifier",e),"string"!=typeof(e=h.escape.string(e))&&h.error(s.identifier,e),0<n.filter("#"+e).length||(0<n.filter('[name="'+e+'"]').length||0<n.filter("[data-"+u.validate+'="'+e+'"]').length)}},escape:{string:function(e){return(e=String(e)).replace(i.escape,"\\$&")}},add:{rule:function(e,t){h.add.field(e,t)},field:function(n,e){var i={};h.is.shorthandRules(e)?(e=F.isArray(e)?e:[e],i[n]={rules:[]},F.each(e,function(e,t){i[n].rules.push({type:t})})):i[n]=e,c=F.extend({},c,i),h.debug("Adding rules",i,c)},fields:function(e){var t;t=e&&h.is.shorthandFields(e)?h.get.fieldsFromShorthand(e):e,c=F.extend({},c,t)},prompt:function(e,t){var n=h.get.field(e).closest(l),i=n.children(f.prompt),o=0!==i.length;t="string"==typeof t?[t]:t,h.verbose("Adding field error state",e),n.addClass(m.error),d.inline&&(o||(i=d.templates.prompt(t)).appendTo(n),i.html(t[0]),o?h.verbose("Inline errors are disabled, no inline error added",e):d.transition&&F.fn.transition!==D&&r.transition("is supported")?(h.verbose("Displaying error with css transition",d.transition),i.transition(d.transition+" in",d.duration)):(h.verbose("Displaying error with fallback javascript animation"),i.fadeIn(d.duration)))},errors:function(e){h.debug("Adding form error messages",e),h.set.error(),t.html(d.templates.error(e))}},remove:{rule:function(n,e){var i=F.isArray(e)?e:[e];if(e==D)return h.debug("Removed all rules"),void(c[n].rules=[]);c[n]!=D&&F.isArray(c[n].rules)&&F.each(c[n].rules,function(e,t){-1!==i.indexOf(t.type)&&(h.debug("Removed rule",t.type),c[n].rules.splice(e,1))})},field:function(e){var t=F.isArray(e)?e:[e];F.each(t,function(e,t){h.remove.rule(t)})},rules:function(e,n){F.isArray(e)?F.each(fields,function(e,t){h.remove.rule(t,n)}):h.remove.rule(e,n)},fields:function(e){h.remove.field(e)},prompt:function(e){var t=h.get.field(e).closest(l),n=t.children(f.prompt);t.removeClass(m.error),d.inline&&n.is(":visible")&&(h.verbose("Removing prompt for field",e),d.transition&&F.fn.transition!==D&&r.transition("is supported")?n.transition(d.transition+" out",d.duration,function(){n.remove()}):n.fadeOut(d.duration,function(){n.remove()}))}},set:{success:function(){r.removeClass(m.error).addClass(m.success)},defaults:function(){n.each(function(){var e=F(this),t=0<e.filter(f.checkbox).length?e.is(":checked"):e.val();e.data(u.defaultValue,t)})},error:function(){r.removeClass(m.success).addClass(m.error)},value:function(e,t){var n={};return n[e]=t,h.set.values.call(v,n)},values:function(e){F.isEmptyObject(e)||F.each(e,function(e,t){var n,i=h.get.field(e),o=i.parent(),a=F.isArray(t),r=o.is(f.uiCheckbox),s=o.is(f.uiDropdown),l=i.is(f.radio)&&r;0<i.length&&(a&&r?(h.verbose("Selecting multiple",t,i),o.checkbox("uncheck"),F.each(t,function(e,t){n=i.filter('[value="'+t+'"]'),o=n.parent(),0<n.length&&o.checkbox("check")})):l?(h.verbose("Selecting radio value",t,i),i.filter('[value="'+t+'"]').parent(f.uiCheckbox).checkbox("check")):r?(h.verbose("Setting checkbox value",t,o),!0===t?o.checkbox("check"):o.checkbox("uncheck")):s?(h.verbose("Setting dropdown value",t,o),o.dropdown("set selected",t)):(h.verbose("Setting field value",t,i),i.val(t)))})}},validate:{form:function(e,t){var n=h.get.values();if(y)return!1;if(b=[],h.determine.isValid()){if(h.debug("Form has no validation errors, submitting"),h.set.success(),!0!==t)return d.onSuccess.call(v,e,n)}else if(h.debug("Form has errors"),h.set.error(),d.inline||h.add.errors(b),r.data("moduleApi")!==D&&e.stopImmediatePropagation(),!0!==t)return d.onFailure.call(v,b,n)},field:function(n,e,t){t=t===D||t,"string"==typeof n&&(h.verbose("Validating field",n),n=c[e=n]);var i=n.identifier||e,o=h.get.field(i),a=!!n.depends&&h.get.field(n.depends),r=!0,s=[];return n.identifier||(h.debug("Using field name as identifier",i),n.identifier=i),o.prop("disabled")?(h.debug("Field is disabled. Skipping",i),r=!0):n.optional&&h.is.blank(o)?(h.debug("Field is optional and blank. Skipping",i),r=!0):n.depends&&h.is.empty(a)?(h.debug("Field depends on another value that is not present or empty. Skipping",a),r=!0):n.rules!==D&&F.each(n.rules,function(e,t){h.has.field(i)&&!h.validate.rule(n,t)&&(h.debug("Field is invalid",i,t.type),s.push(h.get.prompt(t,n)),r=!1)}),r?(t&&(h.remove.prompt(i,s),d.onValid.call(o)),!0):(t&&(b=b.concat(s),h.add.prompt(i,s),d.onInvalid.call(o,s)),!1)},rule:function(e,t){var n=h.get.field(e.identifier),i=(t.type,n.val()),o=h.get.ancillaryValue(t),a=h.get.ruleName(t),r=d.rules[a];if(F.isFunction(r))return i=i===D||""===i||null===i?"":F.trim(i+""),r.call(n,i,o);h.error(s.noRule,a)}},setting:function(e,t){if(F.isPlainObject(e))F.extend(!0,d,e);else{if(t===D)return d[e];d[e]=t}},internal:function(e,t){if(F.isPlainObject(e))F.extend(!0,h,e);else{if(t===D)return h[e];h[e]=t}},debug:function(){!d.silent&&d.debug&&(d.performance?h.performance.log(arguments):(h.debug=Function.prototype.bind.call(console.info,console,d.name+":"),h.debug.apply(console,arguments)))},verbose:function(){!d.silent&&d.verbose&&d.debug&&(d.performance?h.performance.log(arguments):(h.verbose=Function.prototype.bind.call(console.info,console,d.name+":"),h.verbose.apply(console,arguments)))},error:function(){d.silent||(h.error=Function.prototype.bind.call(console.error,console,d.name+":"),h.error.apply(console,arguments))},performance:{log:function(e){var t,n;d.performance&&(n=(t=(new Date).getTime())-(k||t),k=t,T.push({Name:e[0],Arguments:[].slice.call(e,1)||"",Element:v,"Execution Time":n})),clearTimeout(h.performance.timer),h.performance.timer=setTimeout(h.performance.display,500)},display:function(){var e=d.name+":",n=0;k=!1,clearTimeout(h.performance.timer),F.each(T,function(e,t){n+=t["Execution Time"]}),e+=" "+n+"ms",S&&(e+=" '"+S+"'"),1<w.length&&(e+=" ("+w.length+")"),(console.group!==D||console.table!==D)&&0<T.length&&(console.groupCollapsed(e),console.table?console.table(T):F.each(T,function(e,t){console.log(t.Name+": "+t["Execution Time"]+"ms")}),console.groupEnd()),T=[]}},invoke:function(i,e,t){var o,a,n,r=p;return e=e||E,t=v||t,"string"==typeof i&&r!==D&&(i=i.split(/[\. ]/),o=i.length-1,F.each(i,function(e,t){var n=e!=o?t+i[e+1].charAt(0).toUpperCase()+i[e+1].slice(1):i;if(F.isPlainObject(r[n])&&e!=o)r=r[n];else{if(r[n]!==D)return a=r[n],!1;if(!F.isPlainObject(r[t])||e==o)return r[t]!==D&&(a=r[t]),!1;r=r[t]}})),F.isFunction(a)?n=a.apply(t,e):a!==D&&(n=a),F.isArray(C)?C.push(n):C!==D?C=[C,n]:n!==D&&(C=n),a}}).initialize()}),C!==D?C:this},F.fn.form.settings={name:"Form",namespace:"form",debug:!1,verbose:!1,performance:!0,fields:!1,keyboardShortcuts:!0,on:"submit",inline:!1,delay:200,revalidate:!0,transition:"scale",duration:200,onValid:function(){},onInvalid:function(){},onSuccess:function(){return!0},onFailure:function(){return!1},metadata:{defaultValue:"default",validate:"validate"},regExp:{htmlID:/^[a-zA-Z][\w:.-]*$/g,bracket:/\[(.*)\]/i,decimal:/^\d+\.?\d*$/,email:/^[a-z0-9!#$%&'*+\/=?^_`{|}~.-]+@[a-z0-9]([a-z0-9-]*[a-z0-9])?(\.[a-z0-9]([a-z0-9-]*[a-z0-9])?)*$/i,escape:/[\-\[\]\/\{\}\(\)\*\+\?\.\\\^\$\|]/g,flags:/^\/(.*)\/(.*)?/,integer:/^\-?\d+$/,number:/^\-?\d*(\.\d+)?$/,url:/(https?:\/\/(?:www\.|(?!www))[^\s\.]+\.[^\s]{2,}|www\.[^\s]+\.[^\s]{2,})/i},text:{unspecifiedRule:"Please enter a valid value",unspecifiedField:"This field"},prompt:{empty:"{name} must have a value",checked:"{name} must be checked",email:"{name} must be a valid e-mail",url:"{name} must be a valid url",regExp:"{name} is not formatted correctly",integer:"{name} must be an integer",decimal:"{name} must be a decimal number",number:"{name} must be set to a number",is:'{name} must be "{ruleValue}"',isExactly:'{name} must be exactly "{ruleValue}"',not:'{name} cannot be set to "{ruleValue}"',notExactly:'{name} cannot be set to exactly "{ruleValue}"',contain:'{name} must contain "{ruleValue}"',containExactly:'{name} must contain exactly "{ruleValue}"',doesntContain:'{name} cannot contain "{ruleValue}"',doesntContainExactly:'{name} cannot contain exactly "{ruleValue}"',minLength:"{name} must be at least {ruleValue} characters",length:"{name} must be at least {ruleValue} characters",exactLength:"{name} must be exactly {ruleValue} characters",maxLength:"{name} cannot be longer than {ruleValue} characters",match:"{name} must match {ruleValue} field",different:"{name} must have a different value than {ruleValue} field",creditCard:"{name} must be a valid credit card number",minCount:"{name} must have at least {ruleValue} choices",exactCount:"{name} must have exactly {ruleValue} choices",maxCount:"{name} must have {ruleValue} or less choices"},selector:{checkbox:'input[type="checkbox"], input[type="radio"]',clear:".clear",field:"input, textarea, select",group:".field",input:"input",message:".error.message",prompt:".prompt.label",radio:'input[type="radio"]',reset:'.reset:not([type="reset"])',submit:'.submit:not([type="submit"])',uiCheckbox:".ui.checkbox",uiDropdown:".ui.dropdown"},className:{error:"error",label:"ui prompt label",pressed:"down",success:"success"},error:{identifier:"You must specify a string identifier for each field",method:"The method you called is not defined.",noRule:"There is no rule matching the one you specified",oldSyntax:"Starting in 2.0 forms now only take a single settings object. Validation settings converted to new syntax automatically."},templates:{error:function(e){var n='<ul class="list">';return F.each(e,function(e,t){n+="<li>"+t+"</li>"}),F(n+="</ul>")},prompt:function(e){return F("<div/>").addClass("ui basic red pointing prompt label").html(e[0])}},rules:{empty:function(e){return!(e===D||""===e||F.isArray(e)&&0===e.length)},checked:function(){return 0<F(this).filter(":checked").length},email:function(e){return F.fn.form.settings.regExp.email.test(e)},url:function(e){return F.fn.form.settings.regExp.url.test(e)},regExp:function(e,t){if(t instanceof RegExp)return e.match(t);var n,i=t.match(F.fn.form.settings.regExp.flags);return i&&(t=2<=i.length?i[1]:t,n=3<=i.length?i[2]:""),e.match(new RegExp(t,n))},integer:function(e,t){var n,i,o,a=F.fn.form.settings.regExp.integer;return t&&-1===["",".."].indexOf(t)&&(-1==t.indexOf("..")?a.test(t)&&(n=i=t-0):(o=t.split("..",2),a.test(o[0])&&(n=o[0]-0),a.test(o[1])&&(i=o[1]-0))),a.test(e)&&(n===D||n<=e)&&(i===D||e<=i)},decimal:function(e){return F.fn.form.settings.regExp.decimal.test(e)},number:function(e){return F.fn.form.settings.regExp.number.test(e)},is:function(e,t){return t="string"==typeof t?t.toLowerCase():t,(e="string"==typeof e?e.toLowerCase():e)==t},isExactly:function(e,t){return e==t},not:function(e,t){return(e="string"==typeof e?e.toLowerCase():e)!=(t="string"==typeof t?t.toLowerCase():t)},notExactly:function(e,t){return e!=t},contains:function(e,t){return t=t.replace(F.fn.form.settings.regExp.escape,"\\$&"),-1!==e.search(new RegExp(t,"i"))},containsExactly:function(e,t){return t=t.replace(F.fn.form.settings.regExp.escape,"\\$&"),-1!==e.search(new RegExp(t))},doesntContain:function(e,t){return t=t.replace(F.fn.form.settings.regExp.escape,"\\$&"),-1===e.search(new RegExp(t,"i"))},doesntContainExactly:function(e,t){return t=t.replace(F.fn.form.settings.regExp.escape,"\\$&"),-1===e.search(new RegExp(t))},minLength:function(e,t){return e!==D&&e.length>=t},length:function(e,t){return e!==D&&e.length>=t},exactLength:function(e,t){return e!==D&&e.length==t},maxLength:function(e,t){return e!==D&&e.length<=t},match:function(e,t){var n;F(this);return 0<F('[data-validate="'+t+'"]').length?n=F('[data-validate="'+t+'"]').val():0<F("#"+t).length?n=F("#"+t).val():0<F('[name="'+t+'"]').length?n=F('[name="'+t+'"]').val():0<F('[name="'+t+'[]"]').length&&(n=F('[name="'+t+'[]"]')),n!==D&&e.toString()==n.toString()},different:function(e,t){var n;F(this);return 0<F('[data-validate="'+t+'"]').length?n=F('[data-validate="'+t+'"]').val():0<F("#"+t).length?n=F("#"+t).val():0<F('[name="'+t+'"]').length?n=F('[name="'+t+'"]').val():0<F('[name="'+t+'[]"]').length&&(n=F('[name="'+t+'[]"]')),n!==D&&e.toString()!==n.toString()},creditCard:function(n,e){var t,i,o={visa:{pattern:/^4/,length:[16]},amex:{pattern:/^3[47]/,length:[15]},mastercard:{pattern:/^5[1-5]/,length:[16]},discover:{pattern:/^(6011|622(12[6-9]|1[3-9][0-9]|[2-8][0-9]{2}|9[0-1][0-9]|92[0-5]|64[4-9])|65)/,length:[16]},unionPay:{pattern:/^(62|88)/,length:[16,17,18,19]},jcb:{pattern:/^35(2[89]|[3-8][0-9])/,length:[16]},maestro:{pattern:/^(5018|5020|5038|6304|6759|676[1-3])/,length:[12,13,14,15,16,17,18,19]},dinersClub:{pattern:/^(30[0-5]|^36)/,length:[14]},laser:{pattern:/^(6304|670[69]|6771)/,length:[16,17,18,19]},visaElectron:{pattern:/^(4026|417500|4508|4844|491(3|7))/,length:[16]}},a={},r=!1,s="string"==typeof e&&e.split(",");if("string"==typeof n&&0!==n.length){if(n=n.replace(/[\-]/g,""),s&&(F.each(s,function(e,t){(i=o[t])&&(a={length:-1!==F.inArray(n.length,i.length),pattern:-1!==n.search(i.pattern)}).length&&a.pattern&&(r=!0)}),!r))return!1;if((t={number:-1!==F.inArray(n.length,o.unionPay.length),pattern:-1!==n.search(o.unionPay.pattern)}).number&&t.pattern)return!0;for(var l=n.length,c=0,u=[[0,1,2,3,4,5,6,7,8,9],[0,2,4,6,8,1,3,5,7,9]],d=0;l--;)d+=u[c][parseInt(n.charAt(l),10)],c^=1;return d%10==0&&0<d}},minCount:function(e,t){return 0==t||(1==t?""!==e:e.split(",").length>=t)},exactCount:function(e,t){return 0==t?""===e:1==t?""!==e&&-1===e.search(","):e.split(",").length==t},maxCount:function(e,t){return 0!=t&&(1==t?-1===e.search(","):e.split(",").length<=t)}}}}(jQuery,window,document),function(S,k,e,T){"use strict";k=void 0!==k&&k.Math==Math?k:"undefined"!=typeof self&&self.Math==Math?self:Function("return this")(),S.fn.accordion=function(a){var v,r=S(this),b=(new Date).getTime(),y=[],x=a,C="string"==typeof x,w=[].slice.call(arguments,1);k.requestAnimationFrame||k.mozRequestAnimationFrame||k.webkitRequestAnimationFrame||k.msRequestAnimationFrame;return r.each(function(){var e,c,u=S.isPlainObject(a)?S.extend(!0,{},S.fn.accordion.settings,a):S.extend({},S.fn.accordion.settings),d=u.className,t=u.namespace,f=u.selector,s=u.error,n="."+t,i="module-"+t,o=r.selector||"",m=S(this),g=m.find(f.title),p=m.find(f.content),l=this,h=m.data(i);c={initialize:function(){c.debug("Initializing",m),c.bind.events(),u.observeChanges&&c.observeChanges(),c.instantiate()},instantiate:function(){h=c,m.data(i,c)},destroy:function(){c.debug("Destroying previous instance",m),m.off(n).removeData(i)},refresh:function(){g=m.find(f.title),p=m.find(f.content)},observeChanges:function(){"MutationObserver"in k&&((e=new MutationObserver(function(e){c.debug("DOM tree modified, updating selector cache"),c.refresh()})).observe(l,{childList:!0,subtree:!0}),c.debug("Setting up mutation observer",e))},bind:{events:function(){c.debug("Binding delegated events"),m.on(u.on+n,f.trigger,c.event.click)}},event:{click:function(){c.toggle.call(this)}},toggle:function(e){var t=e!==T?"number"==typeof e?g.eq(e):S(e).closest(f.title):S(this).closest(f.title),n=t.next(p),i=n.hasClass(d.animating),o=n.hasClass(d.active),a=o&&!i,r=!o&&i;c.debug("Toggling visibility of content",t),a||r?u.collapsible?c.close.call(t):c.debug("Cannot close accordion content collapsing is disabled"):c.open.call(t)},open:function(e){var t=e!==T?"number"==typeof e?g.eq(e):S(e).closest(f.title):S(this).closest(f.title),n=t.next(p),i=n.hasClass(d.animating);n.hasClass(d.active)||i?c.debug("Accordion already open, skipping",n):(c.debug("Opening accordion content",t),u.onOpening.call(n),u.onChanging.call(n),u.exclusive&&c.closeOthers.call(t),t.addClass(d.active),n.stop(!0,!0).addClass(d.animating),u.animateChildren&&(S.fn.transition!==T&&m.transition("is supported")?n.children().transition({animation:"fade in",queue:!1,useFailSafe:!0,debug:u.debug,verbose:u.verbose,duration:u.duration}):n.children().stop(!0,!0).animate({opacity:1},u.duration,c.resetOpacity)),n.slideDown(u.duration,u.easing,function(){n.removeClass(d.animating).addClass(d.active),c.reset.display.call(this),u.onOpen.call(this),u.onChange.call(this)}))},close:function(e){var t=e!==T?"number"==typeof e?g.eq(e):S(e).closest(f.title):S(this).closest(f.title),n=t.next(p),i=n.hasClass(d.animating),o=n.hasClass(d.active);!o&&!(!o&&i)||o&&i||(c.debug("Closing accordion content",n),u.onClosing.call(n),u.onChanging.call(n),t.removeClass(d.active),n.stop(!0,!0).addClass(d.animating),u.animateChildren&&(S.fn.transition!==T&&m.transition("is supported")?n.children().transition({animation:"fade out",queue:!1,useFailSafe:!0,debug:u.debug,verbose:u.verbose,duration:u.duration}):n.children().stop(!0,!0).animate({opacity:0},u.duration,c.resetOpacity)),n.slideUp(u.duration,u.easing,function(){n.removeClass(d.animating).removeClass(d.active),c.reset.display.call(this),u.onClose.call(this),u.onChange.call(this)}))},closeOthers:function(e){var t,n,i,o=e!==T?g.eq(e):S(this).closest(f.title),a=o.parents(f.content).prev(f.title),r=o.closest(f.accordion),s=f.title+"."+d.active+":visible",l=f.content+"."+d.active+":visible";i=u.closeNested?(t=r.find(s).not(a)).next(p):(t=r.find(s).not(a),n=r.find(l).find(s).not(a),(t=t.not(n)).next(p)),0<t.length&&(c.debug("Exclusive enabled, closing other content",t),t.removeClass(d.active),i.removeClass(d.animating).stop(!0,!0),u.animateChildren&&(S.fn.transition!==T&&m.transition("is supported")?i.children().transition({animation:"fade out",useFailSafe:!0,debug:u.debug,verbose:u.verbose,duration:u.duration}):i.children().stop(!0,!0).animate({opacity:0},u.duration,c.resetOpacity)),i.slideUp(u.duration,u.easing,function(){S(this).removeClass(d.active),c.reset.display.call(this)}))},reset:{display:function(){c.verbose("Removing inline display from element",this),S(this).css("display",""),""===S(this).attr("style")&&S(this).attr("style","").removeAttr("style")},opacity:function(){c.verbose("Removing inline opacity from element",this),S(this).css("opacity",""),""===S(this).attr("style")&&S(this).attr("style","").removeAttr("style")}},setting:function(e,t){if(c.debug("Changing setting",e,t),S.isPlainObject(e))S.extend(!0,u,e);else{if(t===T)return u[e];S.isPlainObject(u[e])?S.extend(!0,u[e],t):u[e]=t}},internal:function(e,t){if(c.debug("Changing internal",e,t),t===T)return c[e];S.isPlainObject(e)?S.extend(!0,c,e):c[e]=t},debug:function(){!u.silent&&u.debug&&(u.performance?c.performance.log(arguments):(c.debug=Function.prototype.bind.call(console.info,console,u.name+":"),c.debug.apply(console,arguments)))},verbose:function(){!u.silent&&u.verbose&&u.debug&&(u.performance?c.performance.log(arguments):(c.verbose=Function.prototype.bind.call(console.info,console,u.name+":"),c.verbose.apply(console,arguments)))},error:function(){u.silent||(c.error=Function.prototype.bind.call(console.error,console,u.name+":"),c.error.apply(console,arguments))},performance:{log:function(e){var t,n;u.performance&&(n=(t=(new Date).getTime())-(b||t),b=t,y.push({Name:e[0],Arguments:[].slice.call(e,1)||"",Element:l,"Execution Time":n})),clearTimeout(c.performance.timer),c.performance.timer=setTimeout(c.performance.display,500)},display:function(){var e=u.name+":",n=0;b=!1,clearTimeout(c.performance.timer),S.each(y,function(e,t){n+=t["Execution Time"]}),e+=" "+n+"ms",o&&(e+=" '"+o+"'"),(console.group!==T||console.table!==T)&&0<y.length&&(console.groupCollapsed(e),console.table?console.table(y):S.each(y,function(e,t){console.log(t.Name+": "+t["Execution Time"]+"ms")}),console.groupEnd()),y=[]}},invoke:function(i,e,t){var o,a,n,r=h;return e=e||w,t=l||t,"string"==typeof i&&r!==T&&(i=i.split(/[\. ]/),o=i.length-1,S.each(i,function(e,t){var n=e!=o?t+i[e+1].charAt(0).toUpperCase()+i[e+1].slice(1):i;if(S.isPlainObject(r[n])&&e!=o)r=r[n];else{if(r[n]!==T)return a=r[n],!1;if(!S.isPlainObject(r[t])||e==o)return r[t]!==T?a=r[t]:c.error(s.method,i),!1;r=r[t]}})),S.isFunction(a)?n=a.apply(t,e):a!==T&&(n=a),S.isArray(v)?v.push(n):v!==T?v=[v,n]:n!==T&&(v=n),a}},C?(h===T&&c.initialize(),c.invoke(x)):(h!==T&&h.invoke("destroy"),c.initialize())}),v!==T?v:this},S.fn.accordion.settings={name:"Accordion",namespace:"accordion",silent:!1,debug:!1,verbose:!1,performance:!0,on:"click",observeChanges:!0,exclusive:!0,collapsible:!0,closeNested:!1,animateChildren:!0,duration:350,easing:"easeOutQuad",onOpening:function(){},onClosing:function(){},onChanging:function(){},onOpen:function(){},onClose:function(){},onChange:function(){},error:{method:"The method you called is not defined"},className:{active:"active",animating:"animating"},selector:{accordion:".accordion",title:".title",trigger:".title",content:".content"}},S.extend(S.easing,{easeOutQuad:function(e,t,n,i,o){return-i*(t/=o)*(t-2)+n}})}(jQuery,window,document),function(T,A,R,P){"use strict";A=void 0!==A&&A.Math==Math?A:"undefined"!=typeof self&&self.Math==Math?self:Function("return this")(),T.fn.checkbox=function(v){var b,e=T(this),y=e.selector||"",x=(new Date).getTime(),C=[],w=v,S="string"==typeof w,k=[].slice.call(arguments,1);return e.each(function(){var e,s,i=T.extend(!0,{},T.fn.checkbox.settings,v),t=i.className,n=i.namespace,o=i.selector,l=i.error,a="."+n,r="module-"+n,c=T(this),u=T(this).children(o.label),d=T(this).children(o.input),f=d[0],m=!1,g=!1,p=c.data(r),h=this;s={initialize:function(){s.verbose("Initializing checkbox",i),s.create.label(),s.bind.events(),s.set.tabbable(),s.hide.input(),s.observeChanges(),s.instantiate(),s.setup()},instantiate:function(){s.verbose("Storing instance of module",s),p=s,c.data(r,s)},destroy:function(){s.verbose("Destroying module"),s.unbind.events(),s.show.input(),c.removeData(r)},fix:{reference:function(){c.is(o.input)&&(s.debug("Behavior called on <input> adjusting invoked element"),c=c.closest(o.checkbox),s.refresh())}},setup:function(){s.set.initialLoad(),s.is.indeterminate()?(s.debug("Initial value is indeterminate"),s.indeterminate()):s.is.checked()?(s.debug("Initial value is checked"),s.check()):(s.debug("Initial value is unchecked"),s.uncheck()),s.remove.initialLoad()},refresh:function(){u=c.children(o.label),d=c.children(o.input),f=d[0]},hide:{input:function(){s.verbose("Modifying <input> z-index to be unselectable"),d.addClass(t.hidden)}},show:{input:function(){s.verbose("Modifying <input> z-index to be selectable"),d.removeClass(t.hidden)}},observeChanges:function(){"MutationObserver"in A&&((e=new MutationObserver(function(e){s.debug("DOM tree modified, updating selector cache"),s.refresh()})).observe(h,{childList:!0,subtree:!0}),s.debug("Setting up mutation observer",e))},attachEvents:function(e,t){var n=T(e);t=T.isFunction(s[t])?s[t]:s.toggle,0<n.length?(s.debug("Attaching checkbox events to element",e,t),n.on("click"+a,t)):s.error(l.notFound)},event:{click:function(e){var t=T(e.target);t.is(o.input)?s.verbose("Using default check action on initialized checkbox"):t.is(o.link)?s.debug("Clicking link inside checkbox, skipping toggle"):(s.toggle(),d.focus(),e.preventDefault())},keydown:function(e){var t=e.which,n=13,i=32;g=t==27?(s.verbose("Escape key pressed blurring field"),d.blur(),!0):!(e.ctrlKey||t!=i&&t!=n)&&(s.verbose("Enter/space key pressed, toggling checkbox"),s.toggle(),!0)},keyup:function(e){g&&e.preventDefault()}},check:function(){s.should.allowCheck()&&(s.debug("Checking checkbox",d),s.set.checked(),s.should.ignoreCallbacks()||(i.onChecked.call(f),i.onChange.call(f)))},uncheck:function(){s.should.allowUncheck()&&(s.debug("Unchecking checkbox"),s.set.unchecked(),s.should.ignoreCallbacks()||(i.onUnchecked.call(f),i.onChange.call(f)))},indeterminate:function(){s.should.allowIndeterminate()?s.debug("Checkbox is already indeterminate"):(s.debug("Making checkbox indeterminate"),s.set.indeterminate(),s.should.ignoreCallbacks()||(i.onIndeterminate.call(f),i.onChange.call(f)))},determinate:function(){s.should.allowDeterminate()?s.debug("Checkbox is already determinate"):(s.debug("Making checkbox determinate"),s.set.determinate(),s.should.ignoreCallbacks()||(i.onDeterminate.call(f),i.onChange.call(f)))},enable:function(){s.is.enabled()?s.debug("Checkbox is already enabled"):(s.debug("Enabling checkbox"),s.set.enabled(),i.onEnable.call(f),i.onEnabled.call(f))},disable:function(){s.is.disabled()?s.debug("Checkbox is already disabled"):(s.debug("Disabling checkbox"),s.set.disabled(),i.onDisable.call(f),i.onDisabled.call(f))},get:{radios:function(){var e=s.get.name();return T('input[name="'+e+'"]').closest(o.checkbox)},otherRadios:function(){return s.get.radios().not(c)},name:function(){return d.attr("name")}},is:{initialLoad:function(){return m},radio:function(){return d.hasClass(t.radio)||"radio"==d.attr("type")},indeterminate:function(){return d.prop("indeterminate")!==P&&d.prop("indeterminate")},checked:function(){return d.prop("checked")!==P&&d.prop("checked")},disabled:function(){return d.prop("disabled")!==P&&d.prop("disabled")},enabled:function(){return!s.is.disabled()},determinate:function(){return!s.is.indeterminate()},unchecked:function(){return!s.is.checked()}},should:{allowCheck:function(){return s.is.determinate()&&s.is.checked()&&!s.should.forceCallbacks()?(s.debug("Should not allow check, checkbox is already checked"),!1):!1!==i.beforeChecked.apply(f)||(s.debug("Should not allow check, beforeChecked cancelled"),!1)},allowUncheck:function(){return s.is.determinate()&&s.is.unchecked()&&!s.should.forceCallbacks()?(s.debug("Should not allow uncheck, checkbox is already unchecked"),!1):!1!==i.beforeUnchecked.apply(f)||(s.debug("Should not allow uncheck, beforeUnchecked cancelled"),!1)},allowIndeterminate:function(){return s.is.indeterminate()&&!s.should.forceCallbacks()?(s.debug("Should not allow indeterminate, checkbox is already indeterminate"),!1):!1!==i.beforeIndeterminate.apply(f)||(s.debug("Should not allow indeterminate, beforeIndeterminate cancelled"),!1)},allowDeterminate:function(){return s.is.determinate()&&!s.should.forceCallbacks()?(s.debug("Should not allow determinate, checkbox is already determinate"),!1):!1!==i.beforeDeterminate.apply(f)||(s.debug("Should not allow determinate, beforeDeterminate cancelled"),!1)},forceCallbacks:function(){return s.is.initialLoad()&&i.fireOnInit},ignoreCallbacks:function(){return m&&!i.fireOnInit}},can:{change:function(){return!(c.hasClass(t.disabled)||c.hasClass(t.readOnly)||d.prop("disabled")||d.prop("readonly"))},uncheck:function(){return"boolean"==typeof i.uncheckable?i.uncheckable:!s.is.radio()}},set:{initialLoad:function(){m=!0},checked:function(){s.verbose("Setting class to checked"),c.removeClass(t.indeterminate).addClass(t.checked),s.is.radio()&&s.uncheckOthers(),s.is.indeterminate()||!s.is.checked()?(s.verbose("Setting state to checked",f),d.prop("indeterminate",!1).prop("checked",!0),s.trigger.change()):s.debug("Input is already checked, skipping input property change")},unchecked:function(){s.verbose("Removing checked class"),c.removeClass(t.indeterminate).removeClass(t.checked),s.is.indeterminate()||!s.is.unchecked()?(s.debug("Setting state to unchecked"),d.prop("indeterminate",!1).prop("checked",!1),s.trigger.change()):s.debug("Input is already unchecked")},indeterminate:function(){s.verbose("Setting class to indeterminate"),c.addClass(t.indeterminate),s.is.indeterminate()?s.debug("Input is already indeterminate, skipping input property change"):(s.debug("Setting state to indeterminate"),d.prop("indeterminate",!0),s.trigger.change())},determinate:function(){s.verbose("Removing indeterminate class"),c.removeClass(t.indeterminate),s.is.determinate()?s.debug("Input is already determinate, skipping input property change"):(s.debug("Setting state to determinate"),d.prop("indeterminate",!1))},disabled:function(){s.verbose("Setting class to disabled"),c.addClass(t.disabled),s.is.disabled()?s.debug("Input is already disabled, skipping input property change"):(s.debug("Setting state to disabled"),d.prop("disabled","disabled"),s.trigger.change())},enabled:function(){s.verbose("Removing disabled class"),c.removeClass(t.disabled),s.is.enabled()?s.debug("Input is already enabled, skipping input property change"):(s.debug("Setting state to enabled"),d.prop("disabled",!1),s.trigger.change())},tabbable:function(){s.verbose("Adding tabindex to checkbox"),d.attr("tabindex")===P&&d.attr("tabindex",0)}},remove:{initialLoad:function(){m=!1}},trigger:{change:function(){var e=R.createEvent("HTMLEvents"),t=d[0];t&&(s.verbose("Triggering native change event"),e.initEvent("change",!0,!1),t.dispatchEvent(e))}},create:{label:function(){0<d.prevAll(o.label).length?(d.prev(o.label).detach().insertAfter(d),s.debug("Moving existing label",u)):s.has.label()||(u=T("<label>").insertAfter(d),s.debug("Creating label",u))}},has:{label:function(){return 0<u.length}},bind:{events:function(){s.verbose("Attaching checkbox events"),c.on("click"+a,s.event.click).on("keydown"+a,o.input,s.event.keydown).on("keyup"+a,o.input,s.event.keyup)}},unbind:{events:function(){s.debug("Removing events"),c.off(a)}},uncheckOthers:function(){var e=s.get.otherRadios();s.debug("Unchecking other radios",e),e.removeClass(t.checked)},toggle:function(){s.can.change()?s.is.indeterminate()||s.is.unchecked()?(s.debug("Currently unchecked"),s.check()):s.is.checked()&&s.can.uncheck()&&(s.debug("Currently checked"),s.uncheck()):s.is.radio()||s.debug("Checkbox is read-only or disabled, ignoring toggle")},setting:function(e,t){if(s.debug("Changing setting",e,t),T.isPlainObject(e))T.extend(!0,i,e);else{if(t===P)return i[e];T.isPlainObject(i[e])?T.extend(!0,i[e],t):i[e]=t}},internal:function(e,t){if(T.isPlainObject(e))T.extend(!0,s,e);else{if(t===P)return s[e];s[e]=t}},debug:function(){!i.silent&&i.debug&&(i.performance?s.performance.log(arguments):(s.debug=Function.prototype.bind.call(console.info,console,i.name+":"),s.debug.apply(console,arguments)))},verbose:function(){!i.silent&&i.verbose&&i.debug&&(i.performance?s.performance.log(arguments):(s.verbose=Function.prototype.bind.call(console.info,console,i.name+":"),s.verbose.apply(console,arguments)))},error:function(){i.silent||(s.error=Function.prototype.bind.call(console.error,console,i.name+":"),s.error.apply(console,arguments))},performance:{log:function(e){var t,n;i.performance&&(n=(t=(new Date).getTime())-(x||t),x=t,C.push({Name:e[0],Arguments:[].slice.call(e,1)||"",Element:h,"Execution Time":n})),clearTimeout(s.performance.timer),s.performance.timer=setTimeout(s.performance.display,500)},display:function(){var e=i.name+":",n=0;x=!1,clearTimeout(s.performance.timer),T.each(C,function(e,t){n+=t["Execution Time"]}),e+=" "+n+"ms",y&&(e+=" '"+y+"'"),(console.group!==P||console.table!==P)&&0<C.length&&(console.groupCollapsed(e),console.table?console.table(C):T.each(C,function(e,t){console.log(t.Name+": "+t["Execution Time"]+"ms")}),console.groupEnd()),C=[]}},invoke:function(i,e,t){var o,a,n,r=p;return e=e||k,t=h||t,"string"==typeof i&&r!==P&&(i=i.split(/[\. ]/),o=i.length-1,T.each(i,function(e,t){var n=e!=o?t+i[e+1].charAt(0).toUpperCase()+i[e+1].slice(1):i;if(T.isPlainObject(r[n])&&e!=o)r=r[n];else{if(r[n]!==P)return a=r[n],!1;if(!T.isPlainObject(r[t])||e==o)return r[t]!==P?a=r[t]:s.error(l.method,i),!1;r=r[t]}})),T.isFunction(a)?n=a.apply(t,e):a!==P&&(n=a),T.isArray(b)?b.push(n):b!==P?b=[b,n]:n!==P&&(b=n),a}},S?(p===P&&s.initialize(),s.invoke(w)):(p!==P&&p.invoke("destroy"),s.initialize())}),b!==P?b:this},T.fn.checkbox.settings={name:"Checkbox",namespace:"checkbox",silent:!1,debug:!1,verbose:!0,performance:!0,uncheckable:"auto",fireOnInit:!1,onChange:function(){},beforeChecked:function(){},beforeUnchecked:function(){},beforeDeterminate:function(){},beforeIndeterminate:function(){},onChecked:function(){},onUnchecked:function(){},onDeterminate:function(){},onIndeterminate:function(){},onEnable:function(){},onDisable:function(){},onEnabled:function(){},onDisabled:function(){},className:{checked:"checked",indeterminate:"indeterminate",disabled:"disabled",hidden:"hidden",radio:"radio",readOnly:"read-only"},error:{method:"The method you called is not defined"},selector:{checkbox:".ui.checkbox",label:"label, .box",input:'input[type="checkbox"], input[type="radio"]',link:"a[href]"}}}(jQuery,window,document),function(S,e,k,T){"use strict";e=void 0!==e&&e.Math==Math?e:"undefined"!=typeof self&&self.Math==Math?self:Function("return this")(),S.fn.dimmer=function(p){var h,v=S(this),b=(new Date).getTime(),y=[],x=p,C="string"==typeof x,w=[].slice.call(arguments,1);return v.each(function(){var a,t,s,r=S.isPlainObject(p)?S.extend(!0,{},S.fn.dimmer.settings,p):S.extend({},S.fn.dimmer.settings),n=r.selector,e=r.namespace,i=r.className,l=r.error,o="."+e,c="module-"+e,u=v.selector||"",d="ontouchstart"in k.documentElement?"touchstart":"click",f=S(this),m=this,g=f.data(c);(s={preinitialize:function(){a=s.is.dimmer()?(t=f.parent(),f):(t=f,s.has.dimmer()?r.dimmerName?t.find(n.dimmer).filter("."+r.dimmerName):t.find(n.dimmer):s.create())},initialize:function(){s.debug("Initializing dimmer",r),s.bind.events(),s.set.dimmable(),s.instantiate()},instantiate:function(){s.verbose("Storing instance of module",s),g=s,f.data(c,g)},destroy:function(){s.verbose("Destroying previous module",a),s.unbind.events(),s.remove.variation(),t.off(o)},bind:{events:function(){"hover"==r.on?t.on("mouseenter"+o,s.show).on("mouseleave"+o,s.hide):"click"==r.on&&t.on(d+o,s.toggle),s.is.page()&&(s.debug("Setting as a page dimmer",t),s.set.pageDimmer()),s.is.closable()&&(s.verbose("Adding dimmer close event",a),t.on(d+o,n.dimmer,s.event.click))}},unbind:{events:function(){f.removeData(c),t.off(o)}},event:{click:function(e){s.verbose("Determining if event occured on dimmer",e),(0===a.find(e.target).length||S(e.target).is(n.content))&&(s.hide(),e.stopImmediatePropagation())}},addContent:function(e){var t=S(e);s.debug("Add content to dimmer",t),t.parent()[0]!==a[0]&&t.detach().appendTo(a)},create:function(){var e=S(r.template.dimmer());return r.dimmerName&&(s.debug("Creating named dimmer",r.dimmerName),e.addClass(r.dimmerName)),e.appendTo(t),e},show:function(e){e=S.isFunction(e)?e:function(){},s.debug("Showing dimmer",a,r),s.set.variation(),s.is.dimmed()&&!s.is.animating()||!s.is.enabled()?s.debug("Dimmer is already shown or disabled"):(s.animate.show(e),r.onShow.call(m),r.onChange.call(m))},hide:function(e){e=S.isFunction(e)?e:function(){},s.is.dimmed()||s.is.animating()?(s.debug("Hiding dimmer",a),s.animate.hide(e),r.onHide.call(m),r.onChange.call(m)):s.debug("Dimmer is not visible")},toggle:function(){s.verbose("Toggling dimmer visibility",a),s.is.dimmed()?s.hide():s.show()},animate:{show:function(e){e=S.isFunction(e)?e:function(){},r.useCSS&&S.fn.transition!==T&&a.transition("is supported")?(r.useFlex?(s.debug("Using flex dimmer"),s.remove.legacy()):(s.debug("Using legacy non-flex dimmer"),s.set.legacy()),"auto"!==r.opacity&&s.set.opacity(),a.transition({displayType:r.useFlex?"flex":"block",animation:r.transition+" in",queue:!1,duration:s.get.duration(),useFailSafe:!0,onStart:function(){s.set.dimmed()},onComplete:function(){s.set.active(),e()}})):(s.verbose("Showing dimmer animation with javascript"),s.set.dimmed(),"auto"==r.opacity&&(r.opacity=.8),a.stop().css({opacity:0,width:"100%",height:"100%"}).fadeTo(s.get.duration(),r.opacity,function(){a.removeAttr("style"),s.set.active(),e()}))},hide:function(e){e=S.isFunction(e)?e:function(){},r.useCSS&&S.fn.transition!==T&&a.transition("is supported")?(s.verbose("Hiding dimmer with css"),a.transition({displayType:r.useFlex?"flex":"block",animation:r.transition+" out",queue:!1,duration:s.get.duration(),useFailSafe:!0,onStart:function(){s.remove.dimmed()},onComplete:function(){s.remove.variation(),s.remove.active(),e()}})):(s.verbose("Hiding dimmer with javascript"),s.remove.dimmed(),a.stop().fadeOut(s.get.duration(),function(){s.remove.active(),a.removeAttr("style"),e()}))}},get:{dimmer:function(){return a},duration:function(){return"object"==typeof r.duration?s.is.active()?r.duration.hide:r.duration.show:r.duration}},has:{dimmer:function(){return r.dimmerName?0<f.find(n.dimmer).filter("."+r.dimmerName).length:0<f.find(n.dimmer).length}},is:{active:function(){return a.hasClass(i.active)},animating:function(){return a.is(":animated")||a.hasClass(i.animating)},closable:function(){return"auto"==r.closable?"hover"!=r.on:r.closable},dimmer:function(){return f.hasClass(i.dimmer)},dimmable:function(){return f.hasClass(i.dimmable)},dimmed:function(){return t.hasClass(i.dimmed)},disabled:function(){return t.hasClass(i.disabled)},enabled:function(){return!s.is.disabled()},page:function(){return t.is("body")},pageDimmer:function(){return a.hasClass(i.pageDimmer)}},can:{show:function(){return!a.hasClass(i.disabled)}},set:{opacity:function(e){var t=a.css("background-color"),n=t.split(","),i=n&&3==n.length,o=n&&4==n.length;e=0===r.opacity?0:r.opacity||e,t=i||o?(n[3]=e+")",n.join(",")):"rgba(0, 0, 0, "+e+")",s.debug("Setting opacity to",e),a.css("background-color",t)},legacy:function(){a.addClass(i.legacy)},active:function(){a.addClass(i.active)},dimmable:function(){t.addClass(i.dimmable)},dimmed:function(){t.addClass(i.dimmed)},pageDimmer:function(){a.addClass(i.pageDimmer)},disabled:function(){a.addClass(i.disabled)},variation:function(e){(e=e||r.variation)&&a.addClass(e)}},remove:{active:function(){a.removeClass(i.active)},legacy:function(){a.removeClass(i.legacy)},dimmed:function(){t.removeClass(i.dimmed)},disabled:function(){a.removeClass(i.disabled)},variation:function(e){(e=e||r.variation)&&a.removeClass(e)}},setting:function(e,t){if(s.debug("Changing setting",e,t),S.isPlainObject(e))S.extend(!0,r,e);else{if(t===T)return r[e];S.isPlainObject(r[e])?S.extend(!0,r[e],t):r[e]=t}},internal:function(e,t){if(S.isPlainObject(e))S.extend(!0,s,e);else{if(t===T)return s[e];s[e]=t}},debug:function(){!r.silent&&r.debug&&(r.performance?s.performance.log(arguments):(s.debug=Function.prototype.bind.call(console.info,console,r.name+":"),s.debug.apply(console,arguments)))},verbose:function(){!r.silent&&r.verbose&&r.debug&&(r.performance?s.performance.log(arguments):(s.verbose=Function.prototype.bind.call(console.info,console,r.name+":"),s.verbose.apply(console,arguments)))},error:function(){r.silent||(s.error=Function.prototype.bind.call(console.error,console,r.name+":"),s.error.apply(console,arguments))},performance:{log:function(e){var t,n;r.performance&&(n=(t=(new Date).getTime())-(b||t),b=t,y.push({Name:e[0],Arguments:[].slice.call(e,1)||"",Element:m,"Execution Time":n})),clearTimeout(s.performance.timer),s.performance.timer=setTimeout(s.performance.display,500)},display:function(){var e=r.name+":",n=0;b=!1,clearTimeout(s.performance.timer),S.each(y,function(e,t){n+=t["Execution Time"]}),e+=" "+n+"ms",u&&(e+=" '"+u+"'"),1<v.length&&(e+=" ("+v.length+")"),(console.group!==T||console.table!==T)&&0<y.length&&(console.groupCollapsed(e),console.table?console.table(y):S.each(y,function(e,t){console.log(t.Name+": "+t["Execution Time"]+"ms")}),console.groupEnd()),y=[]}},invoke:function(i,e,t){var o,a,n,r=g;return e=e||w,t=m||t,"string"==typeof i&&r!==T&&(i=i.split(/[\. ]/),o=i.length-1,S.each(i,function(e,t){var n=e!=o?t+i[e+1].charAt(0).toUpperCase()+i[e+1].slice(1):i;if(S.isPlainObject(r[n])&&e!=o)r=r[n];else{if(r[n]!==T)return a=r[n],!1;if(!S.isPlainObject(r[t])||e==o)return r[t]!==T?a=r[t]:s.error(l.method,i),!1;r=r[t]}})),S.isFunction(a)?n=a.apply(t,e):a!==T&&(n=a),S.isArray(h)?h.push(n):h!==T?h=[h,n]:n!==T&&(h=n),a}}).preinitialize(),C?(g===T&&s.initialize(),s.invoke(x)):(g!==T&&g.invoke("destroy"),s.initialize())}),h!==T?h:this},S.fn.dimmer.settings={name:"Dimmer",namespace:"dimmer",silent:!1,debug:!1,verbose:!1,performance:!0,useFlex:!0,dimmerName:!1,variation:!1,closable:"auto",useCSS:!0,transition:"fade",on:!1,opacity:"auto",duration:{show:500,hide:500},onChange:function(){},onShow:function(){},onHide:function(){},error:{method:"The method you called is not defined."},className:{active:"active",animating:"animating",dimmable:"dimmable",dimmed:"dimmed",dimmer:"dimmer",disabled:"disabled",hide:"hide",legacy:"legacy",pageDimmer:"page",show:"show"},selector:{dimmer:"> .ui.dimmer",content:".ui.dimmer > .content, .ui.dimmer > .content > .center"},template:{dimmer:function(){return S("<div />").attr("class","ui dimmer")}}}}(jQuery,window,document),function(Y,Z,K,J){"use strict";Z=void 0!==Z&&Z.Math==Math?Z:"undefined"!=typeof self&&self.Math==Math?self:Function("return this")(),Y.fn.dropdown=function(M){var L,V=Y(this),N=Y(K),H=V.selector||"",U="ontouchstart"in K.documentElement,W=(new Date).getTime(),B=[],Q=M,X="string"==typeof Q,$=[].slice.call(arguments,1);return V.each(function(n){var e,t,i,o,a,r,s,g,p=Y.isPlainObject(M)?Y.extend(!0,{},Y.fn.dropdown.settings,M):Y.extend({},Y.fn.dropdown.settings),h=p.className,c=p.message,l=p.fields,v=p.keys,b=p.metadata,u=p.namespace,d=p.regExp,y=p.selector,f=p.error,m=p.templates,x="."+u,C="module-"+u,w=Y(this),S=Y(p.context),k=w.find(y.text),T=w.find(y.search),A=w.find(y.sizer),R=w.find(y.input),P=w.find(y.icon),E=0<w.prev().find(y.text).length?w.prev().find(y.text):w.prev(),F=w.children(y.menu),O=F.find(y.item),D=!1,q=!1,j=!1,z=this,I=w.data(C);g={initialize:function(){g.debug("Initializing dropdown",p),g.is.alreadySetup()?g.setup.reference():(g.setup.layout(),p.values&&g.change.values(p.values),g.refreshData(),g.save.defaults(),g.restore.selected(),g.create.id(),g.bind.events(),g.observeChanges(),g.instantiate())},instantiate:function(){g.verbose("Storing instance of dropdown",g),I=g,w.data(C,g)},destroy:function(){g.verbose("Destroying previous dropdown",w),g.remove.tabbable(),w.off(x).removeData(C),F.off(x),N.off(o),g.disconnect.menuObserver(),g.disconnect.selectObserver()},observeChanges:function(){"MutationObserver"in Z&&(r=new MutationObserver(g.event.select.mutation),s=new MutationObserver(g.event.menu.mutation),g.debug("Setting up mutation observer",r,s),g.observe.select(),g.observe.menu())},disconnect:{menuObserver:function(){s&&s.disconnect()},selectObserver:function(){r&&r.disconnect()}},observe:{select:function(){g.has.input()&&r.observe(w[0],{childList:!0,subtree:!0})},menu:function(){g.has.menu()&&s.observe(F[0],{childList:!0,subtree:!0})}},create:{id:function(){a=(Math.random().toString(16)+"000000000").substr(2,8),o="."+a,g.verbose("Creating unique id for element",a)},userChoice:function(e){var n,i,o;return!!(e=e||g.get.userValues())&&(e=Y.isArray(e)?e:[e],Y.each(e,function(e,t){!1===g.get.item(t)&&(o=p.templates.addition(g.add.variables(c.addResult,t)),i=Y("<div />").html(o).attr("data-"+b.value,t).attr("data-"+b.text,t).addClass(h.addition).addClass(h.item),p.hideAdditions&&i.addClass(h.hidden),n=n===J?i:n.add(i),g.verbose("Creating user choices for value",t,i))}),n)},userLabels:function(e){var t=g.get.userValues();t&&(g.debug("Adding user labels",t),Y.each(t,function(e,t){g.verbose("Adding custom user value"),g.add.label(t,t)}))},menu:function(){F=Y("<div />").addClass(h.menu).appendTo(w)},sizer:function(){A=Y("<span />").addClass(h.sizer).insertAfter(T)}},search:function(e){e=e!==J?e:g.get.query(),g.verbose("Searching for query",e),g.has.minCharacters(e)?g.filter(e):g.hide()},select:{firstUnfiltered:function(){g.verbose("Selecting first non-filtered element"),g.remove.selectedItem(),O.not(y.unselectable).not(y.addition+y.hidden).eq(0).addClass(h.selected)},nextAvailable:function(e){var t=(e=e.eq(0)).nextAll(y.item).not(y.unselectable).eq(0),n=e.prevAll(y.item).not(y.unselectable).eq(0);0<t.length?(g.verbose("Moving selection to",t),t.addClass(h.selected)):(g.verbose("Moving selection to",n),n.addClass(h.selected))}},setup:{api:function(){var e={debug:p.debug,urlData:{value:g.get.value(),query:g.get.query()},on:!1};g.verbose("First request, initializing API"),w.api(e)},layout:function(){w.is("select")&&(g.setup.select(),g.setup.returnedObject()),g.has.menu()||g.create.menu(),g.is.search()&&!g.has.search()&&(g.verbose("Adding search input"),T=Y("<input />").addClass(h.search).prop("autocomplete","off").insertBefore(k)),g.is.multiple()&&g.is.searchSelection()&&!g.has.sizer()&&g.create.sizer(),p.allowTab&&g.set.tabbable()},select:function(){var e=g.get.selectValues();g.debug("Dropdown initialized on a select",e),w.is("select")&&(R=w),0<R.parent(y.dropdown).length?(g.debug("UI dropdown already exists. Creating dropdown menu only"),w=R.closest(y.dropdown),g.has.menu()||g.create.menu(),F=w.children(y.menu),g.setup.menu(e)):(g.debug("Creating entire dropdown from select"),w=Y("<div />").attr("class",R.attr("class")).addClass(h.selection).addClass(h.dropdown).html(m.dropdown(e)).insertBefore(R),R.hasClass(h.multiple)&&!1===R.prop("multiple")&&(g.error(f.missingMultiple),R.prop("multiple",!0)),R.is("[multiple]")&&g.set.multiple(),R.prop("disabled")&&(g.debug("Disabling dropdown"),w.addClass(h.disabled)),R.removeAttr("class").detach().prependTo(w)),g.refresh()},menu:function(e){F.html(m.menu(e,l)),O=F.find(y.item)},reference:function(){g.debug("Dropdown behavior was called on select, replacing with closest dropdown"),w=w.parent(y.dropdown),I=w.data(C),z=w.get(0),g.refresh(),g.setup.returnedObject()},returnedObject:function(){var e=V.slice(0,n),t=V.slice(n+1);V=e.add(w).add(t)}},refresh:function(){g.refreshSelectors(),g.refreshData()},refreshItems:function(){O=F.find(y.item)},refreshSelectors:function(){g.verbose("Refreshing selector cache"),k=w.find(y.text),T=w.find(y.search),R=w.find(y.input),P=w.find(y.icon),E=0<w.prev().find(y.text).length?w.prev().find(y.text):w.prev(),F=w.children(y.menu),O=F.find(y.item)},refreshData:function(){g.verbose("Refreshing cached metadata"),O.removeData(b.text).removeData(b.value)},clearData:function(){g.verbose("Clearing metadata"),O.removeData(b.text).removeData(b.value),w.removeData(b.defaultText).removeData(b.defaultValue).removeData(b.placeholderText)},toggle:function(){g.verbose("Toggling menu visibility"),g.is.active()?g.hide():g.show()},show:function(e){if(e=Y.isFunction(e)?e:function(){},!g.can.show()&&g.is.remote()&&(g.debug("No API results retrieved, searching before show"),g.queryRemote(g.get.query(),g.show)),g.can.show()&&!g.is.active()){if(g.debug("Showing dropdown"),!g.has.message()||g.has.maxSelections()||g.has.allResultsFiltered()||g.remove.message(),g.is.allFiltered())return!0;!1!==p.onShow.call(z)&&g.animate.show(function(){g.can.click()&&g.bind.intent(),g.has.menuSearch()&&g.focusSearch(),g.set.visible(),e.call(z)})}},hide:function(e){e=Y.isFunction(e)?e:function(){},g.is.active()&&!g.is.animatingOutward()&&(g.debug("Hiding dropdown"),!1!==p.onHide.call(z)&&g.animate.hide(function(){g.remove.visible(),e.call(z)}))},hideOthers:function(){g.verbose("Finding other dropdowns to hide"),V.not(w).has(y.menu+"."+h.visible).dropdown("hide")},hideMenu:function(){g.verbose("Hiding menu  instantaneously"),g.remove.active(),g.remove.visible(),F.transition("hide")},hideSubMenus:function(){var e=F.children(y.item).find(y.menu);g.verbose("Hiding sub menus",e),e.transition("hide")},bind:{events:function(){U&&g.bind.touchEvents(),g.bind.keyboardEvents(),g.bind.inputEvents(),g.bind.mouseEvents()},touchEvents:function(){g.debug("Touch device detected binding additional touch events"),g.is.searchSelection()||g.is.single()&&w.on("touchstart"+x,g.event.test.toggle),F.on("touchstart"+x,y.item,g.event.item.mouseenter)},keyboardEvents:function(){g.verbose("Binding keyboard events"),w.on("keydown"+x,g.event.keydown),g.has.search()&&w.on(g.get.inputEvent()+x,y.search,g.event.input),g.is.multiple()&&N.on("keydown"+o,g.event.document.keydown)},inputEvents:function(){g.verbose("Binding input change events"),w.on("change"+x,y.input,g.event.change)},mouseEvents:function(){g.verbose("Binding mouse events"),g.is.multiple()&&w.on("click"+x,y.label,g.event.label.click).on("click"+x,y.remove,g.event.remove.click),g.is.searchSelection()?(w.on("mousedown"+x,g.event.mousedown).on("mouseup"+x,g.event.mouseup).on("mousedown"+x,y.menu,g.event.menu.mousedown).on("mouseup"+x,y.menu,g.event.menu.mouseup).on("click"+x,y.icon,g.event.icon.click).on("focus"+x,y.search,g.event.search.focus).on("click"+x,y.search,g.event.search.focus).on("blur"+x,y.search,g.event.search.blur).on("click"+x,y.text,g.event.text.focus),g.is.multiple()&&w.on("click"+x,g.event.click)):("click"==p.on?w.on("click"+x,g.event.test.toggle):"hover"==p.on?w.on("mouseenter"+x,g.delay.show).on("mouseleave"+x,g.delay.hide):w.on(p.on+x,g.toggle),w.on("click"+x,y.icon,g.event.icon.click).on("mousedown"+x,g.event.mousedown).on("mouseup"+x,g.event.mouseup).on("focus"+x,g.event.focus),g.has.menuSearch()?w.on("blur"+x,y.search,g.event.search.blur):w.on("blur"+x,g.event.blur)),F.on("mouseenter"+x,y.item,g.event.item.mouseenter).on("mouseleave"+x,y.item,g.event.item.mouseleave).on("click"+x,y.item,g.event.item.click)},intent:function(){g.verbose("Binding hide intent event to document"),U&&N.on("touchstart"+o,g.event.test.touch).on("touchmove"+o,g.event.test.touch),N.on("click"+o,g.event.test.hide)}},unbind:{intent:function(){g.verbose("Removing hide intent event from document"),U&&N.off("touchstart"+o).off("touchmove"+o),N.off("click"+o)}},filter:function(e){var t=e!==J?e:g.get.query(),n=function(){g.is.multiple()&&g.filterActive(),(e||!e&&0==g.get.activeItem().length)&&g.select.firstUnfiltered(),g.has.allResultsFiltered()?p.onNoResults.call(z,t)?p.allowAdditions?p.hideAdditions&&(g.verbose("User addition with no menu, setting empty style"),g.set.empty(),g.hideMenu()):(g.verbose("All items filtered, showing message",t),g.add.message(c.noResults)):(g.verbose("All items filtered, hiding dropdown",t),g.hideMenu()):(g.remove.empty(),g.remove.message()),p.allowAdditions&&g.add.userSuggestion(e),g.is.searchSelection()&&g.can.show()&&g.is.focusedOnSearch()&&g.show()};p.useLabels&&g.has.maxSelections()||(p.apiSettings?g.can.useAPI()?g.queryRemote(t,function(){p.filterRemoteData&&g.filterItems(t),n()}):g.error(f.noAPI):(g.filterItems(t),n()))},queryRemote:function(e,n){var t={errorDuration:!1,cache:"local",throttle:p.throttle,urlData:{query:e},onError:function(){g.add.message(c.serverError),n()},onFailure:function(){g.add.message(c.serverError),n()},onSuccess:function(e){var t=e[l.remoteValues];Y.isArray(t)&&0<t.length?(g.remove.message(),g.setup.menu({values:e[l.remoteValues]})):g.add.message(c.noResults),n()}};w.api("get request")||g.setup.api(),t=Y.extend(!0,{},t,p.apiSettings),w.api("setting",t).api("query")},filterItems:function(e){var i=e!==J?e:g.get.query(),o=null,t=g.escape.string(i),a=new RegExp("^"+t,"igm");g.has.query()&&(o=[],g.verbose("Searching for matching values",i),O.each(function(){var e,t,n=Y(this);if("both"==p.match||"text"==p.match){if(-1!==(e=String(g.get.choiceText(n,!1))).search(a))return o.push(this),!0;if("exact"===p.fullTextSearch&&g.exactSearch(i,e))return o.push(this),!0;if(!0===p.fullTextSearch&&g.fuzzySearch(i,e))return o.push(this),!0}if("both"==p.match||"value"==p.match){if(-1!==(t=String(g.get.choiceValue(n,e))).search(a))return o.push(this),!0;if("exact"===p.fullTextSearch&&g.exactSearch(i,t))return o.push(this),!0;if(!0===p.fullTextSearch&&g.fuzzySearch(i,t))return o.push(this),!0}})),g.debug("Showing only matched items",i),g.remove.filteredItem(),o&&O.not(o).addClass(h.filtered)},fuzzySearch:function(e,t){var n=t.length,i=e.length;if(e=e.toLowerCase(),t=t.toLowerCase(),n<i)return!1;if(i===n)return e===t;e:for(var o=0,a=0;o<i;o++){for(var r=e.charCodeAt(o);a<n;)if(t.charCodeAt(a++)===r)continue e;return!1}return!0},exactSearch:function(e,t){return e=e.toLowerCase(),-1<(t=t.toLowerCase()).indexOf(e)},filterActive:function(){p.useLabels&&O.filter("."+h.active).addClass(h.filtered)},focusSearch:function(e){g.has.search()&&!g.is.focusedOnSearch()&&(e?(w.off("focus"+x,y.search),T.focus(),w.on("focus"+x,y.search,g.event.search.focus)):T.focus())},forceSelection:function(){var e=O.not(h.filtered).filter("."+h.selected).eq(0),t=O.not(h.filtered).filter("."+h.active).eq(0),n=0<e.length?e:t;if(0<n.length&&!g.is.multiple())return g.debug("Forcing partial selection to selected item",n),void g.event.item.click.call(n,{},!0);p.allowAdditions&&g.set.selected(g.get.query()),g.remove.searchTerm()},change:{values:function(e){p.allowAdditions||g.clear(),g.debug("Creating dropdown with specified values",e),g.setup.menu({values:e}),Y.each(e,function(e,t){if(1==t.selected)return g.debug("Setting initial selection to",t.value),g.set.selected(t.value),!0})}},event:{change:function(){j||(g.debug("Input changed, updating selection"),g.set.selected())},focus:function(){p.showOnFocus&&!D&&g.is.hidden()&&!t&&g.show()},blur:function(e){t=K.activeElement===this,D||t||(g.remove.activeLabel(),g.hide())},mousedown:function(){g.is.searchSelection()?i=!0:D=!0},mouseup:function(){g.is.searchSelection()?i=!1:D=!1},click:function(e){Y(e.target).is(w)&&(g.is.focusedOnSearch()?g.show():g.focusSearch())},search:{focus:function(){D=!0,g.is.multiple()&&g.remove.activeLabel(),p.showOnFocus&&g.search()},blur:function(e){t=K.activeElement===this,g.is.searchSelection()&&!i&&(q||t||(p.forceSelection&&g.forceSelection(),g.hide())),i=!1}},icon:{click:function(e){P.hasClass(h.clear)?g.clear():g.can.click()&&g.toggle()}},text:{focus:function(e){D=!0,g.focusSearch()}},input:function(e){(g.is.multiple()||g.is.searchSelection())&&g.set.filtered(),clearTimeout(g.timer),g.timer=setTimeout(g.search,p.delay.search)},label:{click:function(e){var t=Y(this),n=w.find(y.label),i=n.filter("."+h.active),o=t.nextAll("."+h.active),a=t.prevAll("."+h.active),r=0<o.length?t.nextUntil(o).add(i).add(t):t.prevUntil(a).add(i).add(t);e.shiftKey?(i.removeClass(h.active),r.addClass(h.active)):e.ctrlKey?t.toggleClass(h.active):(i.removeClass(h.active),t.addClass(h.active)),p.onLabelSelect.apply(this,n.filter("."+h.active))}},remove:{click:function(){var e=Y(this).parent();e.hasClass(h.active)?g.remove.activeLabels():g.remove.activeLabels(e)}},test:{toggle:function(e){var t=g.is.multiple()?g.show:g.toggle;g.is.bubbledLabelClick(e)||g.is.bubbledIconClick(e)||g.determine.eventOnElement(e,t)&&e.preventDefault()},touch:function(e){g.determine.eventOnElement(e,function(){"touchstart"==e.type?g.timer=setTimeout(function(){g.hide()},p.delay.touch):"touchmove"==e.type&&clearTimeout(g.timer)}),e.stopPropagation()},hide:function(e){g.determine.eventInModule(e,g.hide)}},select:{mutation:function(e){g.debug("<select> modified, recreating menu");var n=!1;Y.each(e,function(e,t){if(Y(t.target).is("select")||Y(t.addedNodes).is("select"))return n=!0}),n&&(g.disconnect.selectObserver(),g.refresh(),g.setup.select(),g.set.selected(),g.observe.select())}},menu:{mutation:function(e){var t=e[0],n=t.addedNodes?Y(t.addedNodes[0]):Y(!1),i=t.removedNodes?Y(t.removedNodes[0]):Y(!1),o=n.add(i),a=o.is(y.addition)||0<o.closest(y.addition).length,r=o.is(y.message)||0<o.closest(y.message).length;a||r?(g.debug("Updating item selector cache"),g.refreshItems()):(g.debug("Menu modified, updating selector cache"),g.refresh())},mousedown:function(){q=!0},mouseup:function(){q=!1}},item:{mouseenter:function(e){var t=Y(e.target),n=Y(this),i=n.children(y.menu),o=n.siblings(y.item).children(y.menu),a=0<i.length;!(0<i.find(t).length)&&a&&(clearTimeout(g.itemTimer),g.itemTimer=setTimeout(function(){g.verbose("Showing sub-menu",i),Y.each(o,function(){g.animate.hide(!1,Y(this))}),g.animate.show(!1,i)},p.delay.show),e.preventDefault())},mouseleave:function(e){var t=Y(this).children(y.menu);0<t.length&&(clearTimeout(g.itemTimer),g.itemTimer=setTimeout(function(){g.verbose("Hiding sub-menu",t),g.animate.hide(!1,t)},p.delay.hide))},click:function(e,t){var n=Y(this),i=Y(e?e.target:""),o=n.find(y.menu),a=g.get.choiceText(n),r=g.get.choiceValue(n,a),s=0<o.length,l=0<o.find(i).length;g.has.menuSearch()&&Y(K.activeElement).blur(),l||s&&!p.allowCategorySelection||(g.is.searchSelection()&&(p.allowAdditions&&g.remove.userAddition(),g.remove.searchTerm(),g.is.focusedOnSearch()||1==t||g.focusSearch(!0)),p.useLabels||(g.remove.filteredItem(),g.set.scrollPosition(n)),g.determine.selectAction.call(this,a,r))}},document:{keydown:function(e){var t=e.which;if(g.is.inObject(t,v)){var n=w.find(y.label),i=n.filter("."+h.active),o=(i.data(b.value),n.index(i)),a=n.length,r=0<i.length,s=1<i.length,l=0===o,c=o+1==a,u=g.is.searchSelection(),d=g.is.focusedOnSearch(),f=g.is.focused(),m=d&&0===g.get.caretPosition();if(u&&!r&&!d)return;t==v.leftArrow?!f&&!m||r?r&&(e.shiftKey?g.verbose("Adding previous label to selection"):(g.verbose("Selecting previous label"),n.removeClass(h.active)),l&&!s?i.addClass(h.active):i.prev(y.siblingLabel).addClass(h.active).end(),e.preventDefault()):(g.verbose("Selecting previous label"),n.last().addClass(h.active)):t==v.rightArrow?(f&&!r&&n.first().addClass(h.active),r&&(e.shiftKey?g.verbose("Adding next label to selection"):(g.verbose("Selecting next label"),n.removeClass(h.active)),c?u?d?n.removeClass(h.active):g.focusSearch():s?i.next(y.siblingLabel).addClass(h.active):i.addClass(h.active):i.next(y.siblingLabel).addClass(h.active),e.preventDefault())):t==v.deleteKey||t==v.backspace?r?(g.verbose("Removing active labels"),c&&u&&!d&&g.focusSearch(),i.last().next(y.siblingLabel).addClass(h.active),g.remove.activeLabels(i),e.preventDefault()):m&&!r&&t==v.backspace&&(g.verbose("Removing last label on input backspace"),i=n.last().addClass(h.active),g.remove.activeLabels(i)):i.removeClass(h.active)}}},keydown:function(e){var t=e.which;if(g.is.inObject(t,v)){var n,i=O.not(y.unselectable).filter("."+h.selected).eq(0),o=F.children("."+h.active).eq(0),a=0<i.length?i:o,r=0<a.length?a.siblings(":not(."+h.filtered+")").addBack():F.children(":not(."+h.filtered+")"),s=a.children(y.menu),l=a.closest(y.menu),c=l.hasClass(h.visible)||l.hasClass(h.animating)||0<l.parent(y.menu).length,u=0<s.length,d=0<a.length,f=0<a.not(y.unselectable).length,m=t==v.delimiter&&p.allowAdditions&&g.is.multiple();if(p.allowAdditions&&p.hideAdditions&&(t==v.enter||m)&&f&&(g.verbose("Selecting item from keyboard shortcut",a),g.event.item.click.call(a,e),g.is.searchSelection()&&g.remove.searchTerm()),g.is.visible()){if((t==v.enter||m)&&(t==v.enter&&d&&u&&!p.allowCategorySelection?(g.verbose("Pressed enter on unselectable category, opening sub menu"),t=v.rightArrow):f&&(g.verbose("Selecting item from keyboard shortcut",a),g.event.item.click.call(a,e),g.is.searchSelection()&&g.remove.searchTerm()),e.preventDefault()),d&&(t==v.leftArrow&&l[0]!==F[0]&&(g.verbose("Left key pressed, closing sub-menu"),g.animate.hide(!1,l),a.removeClass(h.selected),l.closest(y.item).addClass(h.selected),e.preventDefault()),t==v.rightArrow&&u&&(g.verbose("Right key pressed, opening sub-menu"),g.animate.show(!1,s),a.removeClass(h.selected),s.find(y.item).eq(0).addClass(h.selected),e.preventDefault())),t==v.upArrow){if(n=d&&c?a.prevAll(y.item+":not("+y.unselectable+")").eq(0):O.eq(0),r.index(n)<0)return g.verbose("Up key pressed but reached top of current menu"),void e.preventDefault();g.verbose("Up key pressed, changing active item"),a.removeClass(h.selected),n.addClass(h.selected),g.set.scrollPosition(n),p.selectOnKeydown&&g.is.single()&&g.set.selectedItem(n),e.preventDefault()}if(t==v.downArrow){if(0===(n=d&&c?n=a.nextAll(y.item+":not("+y.unselectable+")").eq(0):O.eq(0)).length)return g.verbose("Down key pressed but reached bottom of current menu"),void e.preventDefault();g.verbose("Down key pressed, changing active item"),O.removeClass(h.selected),n.addClass(h.selected),g.set.scrollPosition(n),p.selectOnKeydown&&g.is.single()&&g.set.selectedItem(n),e.preventDefault()}t==v.pageUp&&(g.scrollPage("up"),e.preventDefault()),t==v.pageDown&&(g.scrollPage("down"),e.preventDefault()),t==v.escape&&(g.verbose("Escape key pressed, closing dropdown"),g.hide())}else m&&e.preventDefault(),t!=v.downArrow||g.is.visible()||(g.verbose("Down key pressed, showing dropdown"),g.show(),e.preventDefault())}else g.has.search()||g.set.selectedLetter(String.fromCharCode(t))}},trigger:{change:function(){var e=K.createEvent("HTMLEvents"),t=R[0];t&&(g.verbose("Triggering native change event"),e.initEvent("change",!0,!1),t.dispatchEvent(e))}},determine:{selectAction:function(e,t){g.verbose("Determining action",p.action),Y.isFunction(g.action[p.action])?(g.verbose("Triggering preset action",p.action,e,t),g.action[p.action].call(z,e,t,this)):Y.isFunction(p.action)?(g.verbose("Triggering user action",p.action,e,t),p.action.call(z,e,t,this)):g.error(f.action,p.action)},eventInModule:function(e,t){var n=Y(e.target),i=0<n.closest(K.documentElement).length,o=0<n.closest(w).length;return t=Y.isFunction(t)?t:function(){},i&&!o?(g.verbose("Triggering event",t),t(),!0):(g.verbose("Event occurred in dropdown, canceling callback"),!1)},eventOnElement:function(e,t){var n=Y(e.target),i=n.closest(y.siblingLabel),o=K.body.contains(e.target),a=0===w.find(i).length,r=0===n.closest(F).length;return t=Y.isFunction(t)?t:function(){},o&&a&&r?(g.verbose("Triggering event",t),t(),!0):(g.verbose("Event occurred in dropdown menu, canceling callback"),!1)}},action:{nothing:function(){},activate:function(e,t,n){if(t=t!==J?t:e,g.can.activate(Y(n))){if(g.set.selected(t,Y(n)),g.is.multiple()&&!g.is.allFiltered())return;g.hideAndClear()}},select:function(e,t,n){if(t=t!==J?t:e,g.can.activate(Y(n))){if(g.set.value(t,e,Y(n)),g.is.multiple()&&!g.is.allFiltered())return;g.hideAndClear()}},combo:function(e,t,n){t=t!==J?t:e,g.set.selected(t,Y(n)),g.hideAndClear()},hide:function(e,t,n){g.set.value(t,e,Y(n)),g.hideAndClear()}},get:{id:function(){return a},defaultText:function(){return w.data(b.defaultText)},defaultValue:function(){return w.data(b.defaultValue)},placeholderText:function(){return"auto"!=p.placeholder&&"string"==typeof p.placeholder?p.placeholder:w.data(b.placeholderText)||""},text:function(){return k.text()},query:function(){return Y.trim(T.val())},searchWidth:function(e){return e=e!==J?e:T.val(),A.text(e),Math.ceil(A.width()+1)},selectionCount:function(){var e=g.get.values();return g.is.multiple()?Y.isArray(e)?e.length:0:""!==g.get.value()?1:0},transition:function(e){return"auto"==p.transition?g.is.upward(e)?"slide up":"slide down":p.transition},userValues:function(){var e=g.get.values();return!!e&&(e=Y.isArray(e)?e:[e],Y.grep(e,function(e){return!1===g.get.item(e)}))},uniqueArray:function(n){return Y.grep(n,function(e,t){return Y.inArray(e,n)===t})},caretPosition:function(){var e,t,n=T.get(0);return"selectionStart"in n?n.selectionStart:K.selection?(n.focus(),t=(e=K.selection.createRange()).text.length,e.moveStart("character",-n.value.length),e.text.length-t):void 0},value:function(){var e=0<R.length?R.val():w.data(b.value),t=Y.isArray(e)&&1===e.length&&""===e[0];return e===J||t?"":e},values:function(){var e=g.get.value();return""===e?"":!g.has.selectInput()&&g.is.multiple()?"string"==typeof e?e.split(p.delimiter):"":e},remoteValues:function(){var e=g.get.values(),i=!1;return e&&("string"==typeof e&&(e=[e]),Y.each(e,function(e,t){var n=g.read.remoteData(t);g.verbose("Restoring value from session data",n,t),n&&(i||(i={}),i[t]=n)})),i},choiceText:function(e,t){if(t=t!==J?t:p.preserveHTML,e)return 0<e.find(y.menu).length&&(g.verbose("Retrieving text of element with sub-menu"),(e=e.clone()).find(y.menu).remove(),e.find(y.menuIcon).remove()),e.data(b.text)!==J?e.data(b.text):t?Y.trim(e.html()):Y.trim(e.text())},choiceValue:function(e,t){return t=t||g.get.choiceText(e),!!e&&(e.data(b.value)!==J?String(e.data(b.value)):"string"==typeof t?Y.trim(t.toLowerCase()):String(t))},inputEvent:function(){var e=T[0];return!!e&&(e.oninput!==J?"input":e.onpropertychange!==J?"propertychange":"keyup")},selectValues:function(){var o={values:[]};return w.find("option").each(function(){var e=Y(this),t=e.html(),n=e.attr("disabled"),i=e.attr("value")!==J?e.attr("value"):t;"auto"===p.placeholder&&""===i?o.placeholder=t:o.values.push({name:t,value:i,disabled:n})}),p.placeholder&&"auto"!==p.placeholder&&(g.debug("Setting placeholder value to",p.placeholder),o.placeholder=p.placeholder),p.sortSelect?(o.values.sort(function(e,t){return e.name>t.name?1:-1}),g.debug("Retrieved and sorted values from select",o)):g.debug("Retrieved values from select",o),o},activeItem:function(){return O.filter("."+h.active)},selectedItem:function(){var e=O.not(y.unselectable).filter("."+h.selected);return 0<e.length?e:O.eq(0)},itemWithAdditions:function(e){var t=g.get.item(e),n=g.create.userChoice(e);return n&&0<n.length&&(t=0<t.length?t.add(n):n),t},item:function(i,o){var e,a,r=!1;return i=i!==J?i:g.get.values()!==J?g.get.values():g.get.text(),e=a?0<i.length:i!==J&&null!==i,a=g.is.multiple()&&Y.isArray(i),o=""===i||0===i||(o||!1),e&&O.each(function(){var e=Y(this),t=g.get.choiceText(e),n=g.get.choiceValue(e,t);if(null!==n&&n!==J)if(a)-1===Y.inArray(String(n),i)&&-1===Y.inArray(t,i)||(r=r?r.add(e):e);else if(o){if(g.verbose("Ambiguous dropdown value using strict type check",e,i),n===i||t===i)return r=e,!0}else if(String(n)==String(i)||t==i)return g.verbose("Found select item by value",n,i),r=e,!0}),r}},check:{maxSelections:function(e){return!p.maxSelections||((e=e!==J?e:g.get.selectionCount())>=p.maxSelections?(g.debug("Maximum selection count reached"),p.useLabels&&(O.addClass(h.filtered),g.add.message(c.maxSelections)),!0):(g.verbose("No longer at maximum selection count"),g.remove.message(),g.remove.filteredItem(),g.is.searchSelection()&&g.filterItems(),!1))}},restore:{defaults:function(){g.clear(),g.restore.defaultText(),g.restore.defaultValue()},defaultText:function(){var e=g.get.defaultText();e===g.get.placeholderText?(g.debug("Restoring default placeholder text",e),g.set.placeholderText(e)):(g.debug("Restoring default text",e),g.set.text(e))},placeholderText:function(){g.set.placeholderText()},defaultValue:function(){var e=g.get.defaultValue();e!==J&&(g.debug("Restoring default value",e),""!==e?(g.set.value(e),g.set.selected()):(g.remove.activeItem(),g.remove.selectedItem()))},labels:function(){p.allowAdditions&&(p.useLabels||(g.error(f.labels),p.useLabels=!0),g.debug("Restoring selected values"),g.create.userLabels()),g.check.maxSelections()},selected:function(){g.restore.values(),g.is.multiple()?(g.debug("Restoring previously selected values and labels"),g.restore.labels()):g.debug("Restoring previously selected values")},values:function(){g.set.initialLoad(),p.apiSettings&&p.saveRemoteData&&g.get.remoteValues()?g.restore.remoteValues():g.set.selected(),g.remove.initialLoad()},remoteValues:function(){var e=g.get.remoteValues();g.debug("Recreating selected from session data",e),e&&(g.is.single()?Y.each(e,function(e,t){g.set.text(t)}):Y.each(e,function(e,t){g.add.label(e,t)}))}},read:{remoteData:function(e){var t;if(Z.Storage!==J)return(t=sessionStorage.getItem(e))!==J&&t;g.error(f.noStorage)}},save:{defaults:function(){g.save.defaultText(),g.save.placeholderText(),g.save.defaultValue()},defaultValue:function(){var e=g.get.value();g.verbose("Saving default value as",e),w.data(b.defaultValue,e)},defaultText:function(){var e=g.get.text();g.verbose("Saving default text as",e),w.data(b.defaultText,e)},placeholderText:function(){var e;!1!==p.placeholder&&k.hasClass(h.placeholder)&&(e=g.get.text(),g.verbose("Saving placeholder text as",e),w.data(b.placeholderText,e))},remoteData:function(e,t){Z.Storage!==J?(g.verbose("Saving remote data to session storage",t,e),sessionStorage.setItem(t,e)):g.error(f.noStorage)}},clear:function(){g.is.multiple()&&p.useLabels?g.remove.labels():(g.remove.activeItem(),g.remove.selectedItem()),g.set.placeholderText(),g.clearValue()},clearValue:function(){g.set.value("")},scrollPage:function(e,t){var n,i,o=t||g.get.selectedItem(),a=o.closest(y.menu),r=a.outerHeight(),s=a.scrollTop(),l=O.eq(0).outerHeight(),c=Math.floor(r/l),u=(a.prop("scrollHeight"),"up"==e?s-l*c:s+l*c),d=O.not(y.unselectable);i="up"==e?d.index(o)-c:d.index(o)+c,0<(n=("up"==e?0<=i:i<d.length)?d.eq(i):"up"==e?d.first():d.last()).length&&(g.debug("Scrolling page",e,n),o.removeClass(h.selected),n.addClass(h.selected),p.selectOnKeydown&&g.is.single()&&g.set.selectedItem(n),a.scrollTop(u))},set:{filtered:function(){var e=g.is.multiple(),t=g.is.searchSelection(),n=e&&t,i=t?g.get.query():"",o="string"==typeof i&&0<i.length,a=g.get.searchWidth(),r=""!==i;e&&o&&(g.verbose("Adjusting input width",a,p.glyphWidth),T.css("width",a)),o||n&&r?(g.verbose("Hiding placeholder text"),k.addClass(h.filtered)):(!e||n&&!r)&&(g.verbose("Showing placeholder text"),k.removeClass(h.filtered))},empty:function(){w.addClass(h.empty)},loading:function(){w.addClass(h.loading)},placeholderText:function(e){e=e||g.get.placeholderText(),g.debug("Setting placeholder text",e),g.set.text(e),k.addClass(h.placeholder)},tabbable:function(){g.is.searchSelection()?(g.debug("Added tabindex to searchable dropdown"),T.val("").attr("tabindex",0),F.attr("tabindex",-1)):(g.debug("Added tabindex to dropdown"),w.attr("tabindex")===J&&(w.attr("tabindex",0),F.attr("tabindex",-1)))},initialLoad:function(){g.verbose("Setting initial load"),e=!0},activeItem:function(e){p.allowAdditions&&0<e.filter(y.addition).length?e.addClass(h.filtered):e.addClass(h.active)},partialSearch:function(e){var t=g.get.query().length;T.val(e.substr(0,t))},scrollPosition:function(e,t){var n,i,o,a,r,s;n=(e=e||g.get.selectedItem()).closest(y.menu),i=e&&0<e.length,t=t!==J&&t,e&&0<n.length&&i&&(e.position().top,n.addClass(h.loading),o=(a=n.scrollTop())-n.offset().top+e.offset().top,t||(s=a+n.height()<o+5,r=o-5<a),g.debug("Scrolling to active item",o),(t||r||s)&&n.scrollTop(o),n.removeClass(h.loading))},text:function(e){"select"!==p.action&&("combo"==p.action?(g.debug("Changing combo button text",e,E),p.preserveHTML?E.html(e):E.text(e)):(e!==g.get.placeholderText()&&k.removeClass(h.placeholder),g.debug("Changing text",e,k),k.removeClass(h.filtered),p.preserveHTML?k.html(e):k.text(e)))},selectedItem:function(e){var t=g.get.choiceValue(e),n=g.get.choiceText(e,!1),i=g.get.choiceText(e,!0);g.debug("Setting user selection to item",e),g.remove.activeItem(),g.set.partialSearch(n),g.set.activeItem(e),g.set.selected(t,e),g.set.text(i)},selectedLetter:function(e){var t,n=O.filter("."+h.selected),i=0<n.length&&g.has.firstLetter(n,e),o=!1;i&&(t=n.nextAll(O).eq(0),g.has.firstLetter(t,e)&&(o=t)),o||O.each(function(){if(g.has.firstLetter(Y(this),e))return o=Y(this),!1}),o&&(g.verbose("Scrolling to next value with letter",e),g.set.scrollPosition(o),n.removeClass(h.selected),o.addClass(h.selected),p.selectOnKeydown&&g.is.single()&&g.set.selectedItem(o))},direction:function(e){"auto"==p.direction?(g.remove.upward(),g.can.openDownward(e)?g.remove.upward(e):g.set.upward(e),g.is.leftward(e)||g.can.openRightward(e)||g.set.leftward(e)):"upward"==p.direction&&g.set.upward(e)},upward:function(e){(e||w).addClass(h.upward)},leftward:function(e){(e||F).addClass(h.leftward)},value:function(e,t,n){var i=g.escape.value(e),o=0<R.length,a=g.get.values(),r=e!==J?String(e):e;if(o){if(!p.allowReselection&&r==a&&(g.verbose("Skipping value update already same value",e,a),!g.is.initialLoad()))return;g.is.single()&&g.has.selectInput()&&g.can.extendSelect()&&(g.debug("Adding user option",e),g.add.optionValue(e)),g.debug("Updating input value",i,a),j=!0,R.val(i),!1===p.fireOnInit&&g.is.initialLoad()?g.debug("Input native change event ignored on initial load"):g.trigger.change(),j=!1}else g.verbose("Storing value in metadata",i,R),i!==a&&w.data(b.value,r);g.is.single()&&p.clearable&&(i?g.set.clearable():g.remove.clearable()),!1===p.fireOnInit&&g.is.initialLoad()?g.verbose("No callback on initial load",p.onChange):p.onChange.call(z,e,t,n)},active:function(){w.addClass(h.active)},multiple:function(){w.addClass(h.multiple)},visible:function(){w.addClass(h.visible)},exactly:function(e,t){g.debug("Setting selected to exact values"),g.clear(),g.set.selected(e,t)},selected:function(e,s){var l=g.is.multiple();(s=p.allowAdditions?s||g.get.itemWithAdditions(e):s||g.get.item(e))&&(g.debug("Setting selected menu item to",s),g.is.multiple()&&g.remove.searchWidth(),g.is.single()?(g.remove.activeItem(),g.remove.selectedItem()):p.useLabels&&g.remove.selectedItem(),s.each(function(){var e=Y(this),t=g.get.choiceText(e),n=g.get.choiceValue(e,t),i=e.hasClass(h.filtered),o=e.hasClass(h.active),a=e.hasClass(h.addition),r=l&&1==s.length;l?!o||a?(p.apiSettings&&p.saveRemoteData&&g.save.remoteData(t,n),p.useLabels?(g.add.label(n,t,r),g.add.value(n,t,e),g.set.activeItem(e),g.filterActive(),g.select.nextAvailable(s)):(g.add.value(n,t,e),g.set.text(g.add.variables(c.count)),g.set.activeItem(e))):i||(g.debug("Selected active value, removing label"),g.remove.selected(n)):(p.apiSettings&&p.saveRemoteData&&g.save.remoteData(t,n),g.set.text(t),g.set.value(n,t,e),e.addClass(h.active).addClass(h.selected))}))},clearable:function(){P.addClass(h.clear)}},add:{label:function(e,t,n){var i,o=g.is.searchSelection()?T:k,a=g.escape.value(e);p.ignoreCase&&(a=a.toLowerCase()),i=Y("<a />").addClass(h.label).attr("data-"+b.value,a).html(m.label(a,t)),i=p.onLabelCreate.call(i,a,t),g.has.label(e)?g.debug("User selection already exists, skipping",a):(p.label.variation&&i.addClass(p.label.variation),!0===n?(g.debug("Animating in label",i),i.addClass(h.hidden).insertBefore(o).transition(p.label.transition,p.label.duration)):(g.debug("Adding selection label",i),i.insertBefore(o)))},message:function(e){var t=F.children(y.message),n=p.templates.message(g.add.variables(e));0<t.length?t.html(n):t=Y("<div/>").html(n).addClass(h.message).appendTo(F)},optionValue:function(e){var t=g.escape.value(e);0<R.find('option[value="'+g.escape.string(t)+'"]').length||(g.disconnect.selectObserver(),g.is.single()&&(g.verbose("Removing previous user addition"),R.find("option."+h.addition).remove()),Y("<option/>").prop("value",t).addClass(h.addition).html(e).appendTo(R),g.verbose("Adding user addition as an <option>",e),g.observe.select())},userSuggestion:function(e){var t,n=F.children(y.addition),i=g.get.item(e),o=i&&i.not(y.addition).length,a=0<n.length;p.useLabels&&g.has.maxSelections()||(""===e||o?n.remove():(a?(n.data(b.value,e).data(b.text,e).attr("data-"+b.value,e).attr("data-"+b.text,e).removeClass(h.filtered),p.hideAdditions||(t=p.templates.addition(g.add.variables(c.addResult,e)),n.html(t)),g.verbose("Replacing user suggestion with new value",n)):((n=g.create.userChoice(e)).prependTo(F),g.verbose("Adding item choice to menu corresponding with user choice addition",n)),p.hideAdditions&&!g.is.allFiltered()||n.addClass(h.selected).siblings().removeClass(h.selected),g.refreshItems()))},variables:function(e,t){var n,i,o=-1!==e.search("{count}"),a=-1!==e.search("{maxCount}"),r=-1!==e.search("{term}");return g.verbose("Adding templated variables to message",e),o&&(n=g.get.selectionCount(),e=e.replace("{count}",n)),a&&(n=g.get.selectionCount(),e=e.replace("{maxCount}",p.maxSelections)),r&&(i=t||g.get.query(),e=e.replace("{term}",i)),e},value:function(e,t,n){var i,o=g.get.values();g.has.value(e)?g.debug("Value already selected"):""!==e?(i=Y.isArray(o)?(i=o.concat([e]),g.get.uniqueArray(i)):[e],g.has.selectInput()?g.can.extendSelect()&&(g.debug("Adding value to select",e,i,R),g.add.optionValue(e)):(i=i.join(p.delimiter),g.debug("Setting hidden input to delimited value",i,R)),!1===p.fireOnInit&&g.is.initialLoad()?g.verbose("Skipping onadd callback on initial load",p.onAdd):p.onAdd.call(z,e,t,n),g.set.value(i,e,t,n),g.check.maxSelections()):g.debug("Cannot select blank values from multiselect")}},remove:{active:function(){w.removeClass(h.active)},activeLabel:function(){w.find(y.label).removeClass(h.active)},empty:function(){w.removeClass(h.empty)},loading:function(){w.removeClass(h.loading)},initialLoad:function(){e=!1},upward:function(e){(e||w).removeClass(h.upward)},leftward:function(e){(e||F).removeClass(h.leftward)},visible:function(){w.removeClass(h.visible)},activeItem:function(){O.removeClass(h.active)},filteredItem:function(){p.useLabels&&g.has.maxSelections()||(p.useLabels&&g.is.multiple()?O.not("."+h.active).removeClass(h.filtered):O.removeClass(h.filtered),g.remove.empty())},optionValue:function(e){var t=g.escape.value(e),n=R.find('option[value="'+g.escape.string(t)+'"]');0<n.length&&n.hasClass(h.addition)&&(r&&(r.disconnect(),g.verbose("Temporarily disconnecting mutation observer")),n.remove(),g.verbose("Removing user addition as an <option>",t),r&&r.observe(R[0],{childList:!0,subtree:!0}))},message:function(){F.children(y.message).remove()},searchWidth:function(){T.css("width","")},searchTerm:function(){g.verbose("Cleared search term"),T.val(""),g.set.filtered()},userAddition:function(){O.filter(y.addition).remove()},selected:function(e,t){if(!(t=p.allowAdditions?t||g.get.itemWithAdditions(e):t||g.get.item(e)))return!1;t.each(function(){var e=Y(this),t=g.get.choiceText(e),n=g.get.choiceValue(e,t);g.is.multiple()?p.useLabels?(g.remove.value(n,t,e),g.remove.label(n)):(g.remove.value(n,t,e),0===g.get.selectionCount()?g.set.placeholderText():g.set.text(g.add.variables(c.count))):g.remove.value(n,t,e),e.removeClass(h.filtered).removeClass(h.active),p.useLabels&&e.removeClass(h.selected)})},selectedItem:function(){O.removeClass(h.selected)},value:function(e,t,n){var i,o=g.get.values();g.has.selectInput()?(g.verbose("Input is <select> removing selected option",e),i=g.remove.arrayValue(e,o),g.remove.optionValue(e)):(g.verbose("Removing from delimited values",e),i=(i=g.remove.arrayValue(e,o)).join(p.delimiter)),!1===p.fireOnInit&&g.is.initialLoad()?g.verbose("No callback on initial load",p.onRemove):p.onRemove.call(z,e,t,n),g.set.value(i,t,n),g.check.maxSelections()},arrayValue:function(t,e){return Y.isArray(e)||(e=[e]),e=Y.grep(e,function(e){return t!=e}),g.verbose("Removed value from delimited string",t,e),e},label:function(e,t){var n=w.find(y.label).filter("[data-"+b.value+'="'+g.escape.string(e)+'"]');g.verbose("Removing label",n),n.remove()},activeLabels:function(e){e=e||w.find(y.label).filter("."+h.active),g.verbose("Removing active label selections",e),g.remove.labels(e)},labels:function(e){e=e||w.find(y.label),g.verbose("Removing labels",e),e.each(function(){var e=Y(this),t=e.data(b.value),n=t!==J?String(t):t,i=g.is.userValue(n);!1!==p.onLabelRemove.call(e,t)?(g.remove.message(),i?(g.remove.value(n),g.remove.label(n)):g.remove.selected(n)):g.debug("Label remove callback cancelled removal")})},tabbable:function(){g.is.searchSelection()?(g.debug("Searchable dropdown initialized"),T.removeAttr("tabindex")):(g.debug("Simple selection dropdown initialized"),w.removeAttr("tabindex")),F.removeAttr("tabindex")},clearable:function(){P.removeClass(h.clear)}},has:{menuSearch:function(){return g.has.search()&&0<T.closest(F).length},search:function(){return 0<T.length},sizer:function(){return 0<A.length},selectInput:function(){return R.is("select")},minCharacters:function(e){return!p.minCharacters||(e=e!==J?String(e):String(g.get.query())).length>=p.minCharacters},firstLetter:function(e,t){var n;return!(!e||0===e.length||"string"!=typeof t)&&(n=g.get.choiceText(e,!1),(t=t.toLowerCase())==String(n).charAt(0).toLowerCase())},input:function(){return 0<R.length},items:function(){return 0<O.length},menu:function(){return 0<F.length},message:function(){return 0!==F.children(y.message).length},label:function(e){var t=g.escape.value(e),n=w.find(y.label);return p.ignoreCase&&(t=t.toLowerCase()),0<n.filter("[data-"+b.value+'="'+g.escape.string(t)+'"]').length},maxSelections:function(){return p.maxSelections&&g.get.selectionCount()>=p.maxSelections},allResultsFiltered:function(){var e=O.not(y.addition);return e.filter(y.unselectable).length===e.length},userSuggestion:function(){return 0<F.children(y.addition).length},query:function(){return""!==g.get.query()},value:function(e){return p.ignoreCase?g.has.valueIgnoringCase(e):g.has.valueMatchingCase(e)},valueMatchingCase:function(e){var t=g.get.values();return!!(Y.isArray(t)?t&&-1!==Y.inArray(e,t):t==e)},valueIgnoringCase:function(n){var e=g.get.values(),i=!1;return Y.isArray(e)||(e=[e]),Y.each(e,function(e,t){if(String(n).toLowerCase()==String(t).toLowerCase())return!(i=!0)}),i}},is:{active:function(){return w.hasClass(h.active)},animatingInward:function(){return F.transition("is inward")},animatingOutward:function(){return F.transition("is outward")},bubbledLabelClick:function(e){return Y(e.target).is("select, input")&&0<w.closest("label").length},bubbledIconClick:function(e){return 0<Y(e.target).closest(P).length},alreadySetup:function(){return w.is("select")&&w.parent(y.dropdown).data(C)!==J&&0===w.prev().length},animating:function(e){return e?e.transition&&e.transition("is animating"):F.transition&&F.transition("is animating")},leftward:function(e){return(e||F).hasClass(h.leftward)},disabled:function(){return w.hasClass(h.disabled)},focused:function(){return K.activeElement===w[0]},focusedOnSearch:function(){return K.activeElement===T[0]},allFiltered:function(){return(g.is.multiple()||g.has.search())&&!(0==p.hideAdditions&&g.has.userSuggestion())&&!g.has.message()&&g.has.allResultsFiltered()},hidden:function(e){return!g.is.visible(e)},initialLoad:function(){return e},inObject:function(n,e){var i=!1;return Y.each(e,function(e,t){if(t==n)return i=!0}),i},multiple:function(){return w.hasClass(h.multiple)},remote:function(){return p.apiSettings&&g.can.useAPI()},single:function(){return!g.is.multiple()},selectMutation:function(e){var n=!1;return Y.each(e,function(e,t){if(t.target&&Y(t.target).is("select"))return n=!0}),n},search:function(){return w.hasClass(h.search)},searchSelection:function(){return g.has.search()&&1===T.parent(y.dropdown).length},selection:function(){return w.hasClass(h.selection)},userValue:function(e){return-1!==Y.inArray(e,g.get.userValues())},upward:function(e){return(e||w).hasClass(h.upward)},visible:function(e){return e?e.hasClass(h.visible):F.hasClass(h.visible)},verticallyScrollableContext:function(){var e=S.get(0)!==Z&&S.css("overflow-y");return"auto"==e||"scroll"==e},horizontallyScrollableContext:function(){var e=S.get(0)!==Z&&S.css("overflow-X");return"auto"==e||"scroll"==e}},can:{activate:function(e){return!!p.useLabels||(!g.has.maxSelections()||!(!g.has.maxSelections()||!e.hasClass(h.active)))},openDownward:function(e){var t,n,i=e||F,o=!0;return i.addClass(h.loading),n={context:{offset:S.get(0)===Z?{top:0,left:0}:S.offset(),scrollTop:S.scrollTop(),height:S.outerHeight()},menu:{offset:i.offset(),height:i.outerHeight()}},g.is.verticallyScrollableContext()&&(n.menu.offset.top+=n.context.scrollTop),o=(t={above:n.context.scrollTop<=n.menu.offset.top-n.context.offset.top-n.menu.height,below:n.context.scrollTop+n.context.height>=n.menu.offset.top-n.context.offset.top+n.menu.height}).below?(g.verbose("Dropdown can fit in context downward",t),!0):t.below||t.above?(g.verbose("Dropdown cannot fit below, opening upward",t),!1):(g.verbose("Dropdown cannot fit in either direction, favoring downward",t),!0),i.removeClass(h.loading),o},openRightward:function(e){var t,n,i=e||F,o=!0;return i.addClass(h.loading),n={context:{offset:S.get(0)===Z?{top:0,left:0}:S.offset(),scrollLeft:S.scrollLeft(),width:S.outerWidth()},menu:{offset:i.offset(),width:i.outerWidth()}},g.is.horizontallyScrollableContext()&&(n.menu.offset.left+=n.context.scrollLeft),(t=n.menu.offset.left-n.context.offset.left+n.menu.width>=n.context.scrollLeft+n.context.width)&&(g.verbose("Dropdown cannot fit in context rightward",t),o=!1),i.removeClass(h.loading),o},click:function(){return U||"click"==p.on},extendSelect:function(){return p.allowAdditions||p.apiSettings},show:function(){return!g.is.disabled()&&(g.has.items()||g.has.message())},useAPI:function(){return Y.fn.api!==J}},animate:{show:function(e,t){var n,i=t||F,o=t?function(){}:function(){g.hideSubMenus(),g.hideOthers(),g.set.active()};e=Y.isFunction(e)?e:function(){},g.verbose("Doing menu show animation",i),g.set.direction(t),n=g.get.transition(t),g.is.selection()&&g.set.scrollPosition(g.get.selectedItem(),!0),(g.is.hidden(i)||g.is.animating(i))&&("none"==n?(o(),i.transition("show"),e.call(z)):Y.fn.transition!==J&&w.transition("is supported")?i.transition({animation:n+" in",debug:p.debug,verbose:p.verbose,duration:p.duration,queue:!0,onStart:o,onComplete:function(){e.call(z)}}):g.error(f.noTransition,n))},hide:function(e,t){var n=t||F,i=(t?p.duration:p.duration,t?function(){}:function(){g.can.click()&&g.unbind.intent(),g.remove.active()}),o=g.get.transition(t);e=Y.isFunction(e)?e:function(){},(g.is.visible(n)||g.is.animating(n))&&(g.verbose("Doing menu hide animation",n),"none"==o?(i(),n.transition("hide"),e.call(z)):Y.fn.transition!==J&&w.transition("is supported")?n.transition({animation:o+" out",duration:p.duration,debug:p.debug,verbose:p.verbose,queue:!1,onStart:i,onComplete:function(){e.call(z)}}):g.error(f.transition))}},hideAndClear:function(){g.remove.searchTerm(),g.has.maxSelections()||(g.has.search()?g.hide(function(){g.remove.filteredItem()}):g.hide())},delay:{show:function(){g.verbose("Delaying show event to ensure user intent"),clearTimeout(g.timer),g.timer=setTimeout(g.show,p.delay.show)},hide:function(){g.verbose("Delaying hide event to ensure user intent"),clearTimeout(g.timer),g.timer=setTimeout(g.hide,p.delay.hide)}},escape:{value:function(e){var t=Y.isArray(e),n="string"==typeof e,i=!n&&!t,o=n&&-1!==e.search(d.quote),a=[];return i||!o?e:(g.debug("Encoding quote values for use in select",e),t?(Y.each(e,function(e,t){a.push(t.replace(d.quote,"&quot;"))}),a):e.replace(d.quote,"&quot;"))},string:function(e){return(e=String(e)).replace(d.escape,"\\$&")}},setting:function(e,t){if(g.debug("Changing setting",e,t),Y.isPlainObject(e))Y.extend(!0,p,e);else{if(t===J)return p[e];Y.isPlainObject(p[e])?Y.extend(!0,p[e],t):p[e]=t}},internal:function(e,t){if(Y.isPlainObject(e))Y.extend(!0,g,e);else{if(t===J)return g[e];g[e]=t}},debug:function(){!p.silent&&p.debug&&(p.performance?g.performance.log(arguments):(g.debug=Function.prototype.bind.call(console.info,console,p.name+":"),g.debug.apply(console,arguments)))},verbose:function(){!p.silent&&p.verbose&&p.debug&&(p.performance?g.performance.log(arguments):(g.verbose=Function.prototype.bind.call(console.info,console,p.name+":"),g.verbose.apply(console,arguments)))},error:function(){p.silent||(g.error=Function.prototype.bind.call(console.error,console,p.name+":"),g.error.apply(console,arguments))},performance:{log:function(e){var t,n;p.performance&&(n=(t=(new Date).getTime())-(W||t),W=t,B.push({Name:e[0],Arguments:[].slice.call(e,1)||"",Element:z,"Execution Time":n})),clearTimeout(g.performance.timer),g.performance.timer=setTimeout(g.performance.display,500)},display:function(){var e=p.name+":",n=0;W=!1,clearTimeout(g.performance.timer),Y.each(B,function(e,t){n+=t["Execution Time"]}),e+=" "+n+"ms",H&&(e+=" '"+H+"'"),(console.group!==J||console.table!==J)&&0<B.length&&(console.groupCollapsed(e),console.table?console.table(B):Y.each(B,function(e,t){console.log(t.Name+": "+t["Execution Time"]+"ms")}),console.groupEnd()),B=[]}},invoke:function(i,e,t){var o,a,n,r=I;return e=e||$,t=z||t,"string"==typeof i&&r!==J&&(i=i.split(/[\. ]/),o=i.length-1,Y.each(i,function(e,t){var n=e!=o?t+i[e+1].charAt(0).toUpperCase()+i[e+1].slice(1):i;if(Y.isPlainObject(r[n])&&e!=o)r=r[n];else{if(r[n]!==J)return a=r[n],!1;if(!Y.isPlainObject(r[t])||e==o)return r[t]!==J?a=r[t]:g.error(f.method,i),!1;r=r[t]}})),Y.isFunction(a)?n=a.apply(t,e):a!==J&&(n=a),Y.isArray(L)?L.push(n):L!==J?L=[L,n]:n!==J&&(L=n),a}},X?(I===J&&g.initialize(),g.invoke(Q)):(I!==J&&I.invoke("destroy"),g.initialize())}),L!==J?L:V},Y.fn.dropdown.settings={silent:!1,debug:!1,verbose:!1,performance:!0,on:"click",action:"activate",values:!1,clearable:!1,apiSettings:!1,selectOnKeydown:!0,minCharacters:0,filterRemoteData:!1,saveRemoteData:!0,throttle:200,context:Z,direction:"auto",keepOnScreen:!0,match:"both",fullTextSearch:!1,placeholder:"auto",preserveHTML:!0,sortSelect:!1,forceSelection:!0,allowAdditions:!1,ignoreCase:!1,hideAdditions:!0,maxSelections:!1,useLabels:!0,delimiter:",",showOnFocus:!0,allowReselection:!1,allowTab:!0,allowCategorySelection:!1,fireOnInit:!1,transition:"auto",duration:200,glyphWidth:1.037,label:{transition:"scale",duration:200,variation:!1},delay:{hide:300,show:200,search:20,touch:50},onChange:function(e,t,n){},onAdd:function(e,t,n){},onRemove:function(e,t,n){},onLabelSelect:function(e){},onLabelCreate:function(e,t){return Y(this)},onLabelRemove:function(e){return!0},onNoResults:function(e){return!0},onShow:function(){},onHide:function(){},name:"Dropdown",namespace:"dropdown",message:{addResult:"Add <b>{term}</b>",count:"{count} selected",maxSelections:"Max {maxCount} selections",noResults:"No results found.",serverError:"There was an error contacting the server"},error:{action:"You called a dropdown action that was not defined",alreadySetup:"Once a select has been initialized behaviors must be called on the created ui dropdown",labels:"Allowing user additions currently requires the use of labels.",missingMultiple:"<select> requires multiple property to be set to correctly preserve multiple values",method:"The method you called is not defined.",noAPI:"The API module is required to load resources remotely",noStorage:"Saving remote data requires session storage",noTransition:"This module requires ui transitions <https://github.com/Semantic-Org/UI-Transition>"},regExp:{escape:/[-[\]{}()*+?.,\\^$|#\s]/g,quote:/"/g},metadata:{defaultText:"defaultText",defaultValue:"defaultValue",placeholderText:"placeholder",text:"text",value:"value"},fields:{remoteValues:"results",values:"values",disabled:"disabled",name:"name",value:"value",text:"text"},keys:{backspace:8,delimiter:188,deleteKey:46,enter:13,escape:27,pageUp:33,pageDown:34,leftArrow:37,upArrow:38,rightArrow:39,downArrow:40},selector:{addition:".addition",dropdown:".ui.dropdown",hidden:".hidden",icon:"> .dropdown.icon",input:'> input[type="hidden"], > select',item:".item",label:"> .label",remove:"> .label > .delete.icon",siblingLabel:".label",menu:".menu",message:".message",menuIcon:".dropdown.icon",search:"input.search, .menu > .search > input, .menu input.search",sizer:"> input.sizer",text:"> .text:not(.icon)",unselectable:".disabled, .filtered"},className:{active:"active",addition:"addition",animating:"animating",clear:"clear",disabled:"disabled",empty:"empty",dropdown:"ui dropdown",filtered:"filtered",hidden:"hidden transition",item:"item",label:"ui label",loading:"loading",menu:"menu",message:"message",multiple:"multiple",placeholder:"default",sizer:"sizer",search:"search",selected:"selected",selection:"selection",upward:"upward",leftward:"left",visible:"visible"}},Y.fn.dropdown.settings.templates={dropdown:function(e){var t=e.placeholder||!1,n=(e.values,"");return n+='<i class="dropdown icon"></i>',e.placeholder?n+='<div class="default text">'+t+"</div>":n+='<div class="text"></div>',n+='<div class="menu">',Y.each(e.values,function(e,t){n+=t.disabled?'<div class="disabled item" data-value="'+t.value+'">'+t.name+"</div>":'<div class="item" data-value="'+t.value+'">'+t.name+"</div>"}),n+="</div>"},menu:function(e,o){var t=e[o.values]||{},a="";return Y.each(t,function(e,t){var n=t[o.text]?'data-text="'+t[o.text]+'"':"",i=t[o.disabled]?"disabled ":"";a+='<div class="'+i+'item" data-value="'+t[o.value]+'"'+n+">",a+=t[o.name],a+="</div>"}),a},label:function(e,t){return t+'<i class="delete icon"></i>'},message:function(e){return e},addition:function(e){return e}}}(jQuery,window,document),function(k,T,e,A){"use strict";T=void 0!==T&&T.Math==Math?T:"undefined"!=typeof self&&self.Math==Math?self:Function("return this")(),k.fn.embed=function(p){var h,v=k(this),b=v.selector||"",y=(new Date).getTime(),x=[],C=p,w="string"==typeof C,S=[].slice.call(arguments,1);return v.each(function(){var s,i=k.isPlainObject(p)?k.extend(!0,{},k.fn.embed.settings,p):k.extend({},k.fn.embed.settings),e=i.selector,t=i.className,o=i.sources,l=i.error,a=i.metadata,n=i.namespace,r=i.templates,c="."+n,u="module-"+n,d=(k(T),k(this)),f=(d.find(e.placeholder),d.find(e.icon),d.find(e.embed)),m=this,g=d.data(u);s={initialize:function(){s.debug("Initializing embed"),s.determine.autoplay(),s.create(),s.bind.events(),s.instantiate()},instantiate:function(){s.verbose("Storing instance of module",s),g=s,d.data(u,s)},destroy:function(){s.verbose("Destroying previous instance of embed"),s.reset(),d.removeData(u).off(c)},refresh:function(){s.verbose("Refreshing selector cache"),d.find(e.placeholder),d.find(e.icon),f=d.find(e.embed)},bind:{events:function(){s.has.placeholder()&&(s.debug("Adding placeholder events"),d.on("click"+c,e.placeholder,s.createAndShow).on("click"+c,e.icon,s.createAndShow))}},create:function(){s.get.placeholder()?s.createPlaceholder():s.createAndShow()},createPlaceholder:function(e){var t=s.get.icon(),n=s.get.url();s.generate.embed(n);e=e||s.get.placeholder(),d.html(r.placeholder(e,t)),s.debug("Creating placeholder for embed",e,t)},createEmbed:function(e){s.refresh(),e=e||s.get.url(),f=k("<div/>").addClass(t.embed).html(s.generate.embed(e)).appendTo(d),i.onCreate.call(m,e),s.debug("Creating embed object",f)},changeEmbed:function(e){f.html(s.generate.embed(e))},createAndShow:function(){s.createEmbed(),s.show()},change:function(e,t,n){s.debug("Changing video to ",e,t,n),d.data(a.source,e).data(a.id,t),n?d.data(a.url,n):d.removeData(a.url),s.has.embed()?s.changeEmbed():s.create()},reset:function(){s.debug("Clearing embed and showing placeholder"),s.remove.data(),s.remove.active(),s.remove.embed(),s.showPlaceholder(),i.onReset.call(m)},show:function(){s.debug("Showing embed"),s.set.active(),i.onDisplay.call(m)},hide:function(){s.debug("Hiding embed"),s.showPlaceholder()},showPlaceholder:function(){s.debug("Showing placeholder image"),s.remove.active(),i.onPlaceholderDisplay.call(m)},get:{id:function(){return i.id||d.data(a.id)},placeholder:function(){return i.placeholder||d.data(a.placeholder)},icon:function(){return i.icon?i.icon:d.data(a.icon)!==A?d.data(a.icon):s.determine.icon()},source:function(e){return i.source?i.source:d.data(a.source)!==A?d.data(a.source):s.determine.source()},type:function(){var e=s.get.source();return o[e]!==A&&o[e].type},url:function(){return i.url?i.url:d.data(a.url)!==A?d.data(a.url):s.determine.url()}},determine:{autoplay:function(){s.should.autoplay()&&(i.autoplay=!0)},source:function(n){var i=!1;return(n=n||s.get.url())&&k.each(o,function(e,t){if(-1!==n.search(t.domain))return i=e,!1}),i},icon:function(){var e=s.get.source();return o[e]!==A&&o[e].icon},url:function(){var e,t=i.id||d.data(a.id),n=i.source||d.data(a.source);return(e=o[n]!==A&&o[n].url.replace("{id}",t))&&d.data(a.url,e),e}},set:{active:function(){d.addClass(t.active)}},remove:{data:function(){d.removeData(a.id).removeData(a.icon).removeData(a.placeholder).removeData(a.source).removeData(a.url)},active:function(){d.removeClass(t.active)},embed:function(){f.empty()}},encode:{parameters:function(e){var t,n=[];for(t in e)n.push(encodeURIComponent(t)+"="+encodeURIComponent(e[t]));return n.join("&amp;")}},generate:{embed:function(e){s.debug("Generating embed html");var t,n,i=s.get.source();return(e=s.get.url(e))?(n=s.generate.parameters(i),t=r.iframe(e,n)):s.error(l.noURL,d),t},parameters:function(e,t){var n=o[e]&&o[e].parameters!==A?o[e].parameters(i):{};return(t=t||i.parameters)&&(n=k.extend({},n,t)),n=i.onEmbed(n),s.encode.parameters(n)}},has:{embed:function(){return 0<f.length},placeholder:function(){return i.placeholder||d.data(a.placeholder)}},should:{autoplay:function(){return"auto"===i.autoplay?i.placeholder||d.data(a.placeholder)!==A:i.autoplay}},is:{video:function(){return"video"==s.get.type()}},setting:function(e,t){if(s.debug("Changing setting",e,t),k.isPlainObject(e))k.extend(!0,i,e);else{if(t===A)return i[e];k.isPlainObject(i[e])?k.extend(!0,i[e],t):i[e]=t}},internal:function(e,t){if(k.isPlainObject(e))k.extend(!0,s,e);else{if(t===A)return s[e];s[e]=t}},debug:function(){!i.silent&&i.debug&&(i.performance?s.performance.log(arguments):(s.debug=Function.prototype.bind.call(console.info,console,i.name+":"),s.debug.apply(console,arguments)))},verbose:function(){!i.silent&&i.verbose&&i.debug&&(i.performance?s.performance.log(arguments):(s.verbose=Function.prototype.bind.call(console.info,console,i.name+":"),s.verbose.apply(console,arguments)))},error:function(){i.silent||(s.error=Function.prototype.bind.call(console.error,console,i.name+":"),s.error.apply(console,arguments))},performance:{log:function(e){var t,n;i.performance&&(n=(t=(new Date).getTime())-(y||t),y=t,x.push({Name:e[0],Arguments:[].slice.call(e,1)||"",Element:m,"Execution Time":n})),clearTimeout(s.performance.timer),s.performance.timer=setTimeout(s.performance.display,500)},display:function(){var e=i.name+":",n=0;y=!1,clearTimeout(s.performance.timer),k.each(x,function(e,t){n+=t["Execution Time"]}),e+=" "+n+"ms",b&&(e+=" '"+b+"'"),1<v.length&&(e+=" ("+v.length+")"),(console.group!==A||console.table!==A)&&0<x.length&&(console.groupCollapsed(e),console.table?console.table(x):k.each(x,function(e,t){console.log(t.Name+": "+t["Execution Time"]+"ms")}),console.groupEnd()),x=[]}},invoke:function(i,e,t){var o,a,n,r=g;return e=e||S,t=m||t,"string"==typeof i&&r!==A&&(i=i.split(/[\. ]/),o=i.length-1,k.each(i,function(e,t){var n=e!=o?t+i[e+1].charAt(0).toUpperCase()+i[e+1].slice(1):i;if(k.isPlainObject(r[n])&&e!=o)r=r[n];else{if(r[n]!==A)return a=r[n],!1;if(!k.isPlainObject(r[t])||e==o)return r[t]!==A?a=r[t]:s.error(l.method,i),!1;r=r[t]}})),k.isFunction(a)?n=a.apply(t,e):a!==A&&(n=a),k.isArray(h)?h.push(n):h!==A?h=[h,n]:n!==A&&(h=n),a}},w?(g===A&&s.initialize(),s.invoke(C)):(g!==A&&g.invoke("destroy"),s.initialize())}),h!==A?h:this},k.fn.embed.settings={name:"Embed",namespace:"embed",silent:!1,debug:!1,verbose:!1,performance:!0,icon:!1,source:!1,url:!1,id:!1,autoplay:"auto",color:"#444444",hd:!0,brandedUI:!1,parameters:!1,onDisplay:function(){},onPlaceholderDisplay:function(){},onReset:function(){},onCreate:function(e){},onEmbed:function(e){return e},metadata:{id:"id",icon:"icon",placeholder:"placeholder",source:"source",url:"url"},error:{noURL:"No URL specified",method:"The method you called is not defined"},className:{active:"active",embed:"embed"},selector:{embed:".embed",placeholder:".placeholder",icon:".icon"},sources:{youtube:{name:"youtube",type:"video",icon:"video play",domain:"youtube.com",url:"//www.youtube.com/embed/{id}",parameters:function(e){return{autohide:!e.brandedUI,autoplay:e.autoplay,color:e.color||A,hq:e.hd,jsapi:e.api,modestbranding:!e.brandedUI}}},vimeo:{name:"vimeo",type:"video",icon:"video play",domain:"vimeo.com",url:"//player.vimeo.com/video/{id}",parameters:function(e){return{api:e.api,autoplay:e.autoplay,byline:e.brandedUI,color:e.color||A,portrait:e.brandedUI,title:e.brandedUI}}}},templates:{iframe:function(e,t){var n=e;return t&&(n+="?"+t),'<iframe src="'+n+'" width="100%" height="100%" frameborder="0" scrolling="no" webkitAllowFullScreen mozallowfullscreen allowFullScreen></iframe>'},placeholder:function(e,t){var n="";return t&&(n+='<i class="'+t+' icon"></i>'),e&&(n+='<img class="placeholder" src="'+e+'">'),n}},api:!1,onPause:function(){},onPlay:function(){},onStop:function(){}}}(jQuery,window,document),function(j,z,I,M){"use strict";z=void 0!==z&&z.Math==Math?z:"undefined"!=typeof self&&self.Math==Math?self:Function("return this")(),j.fn.modal=function(w){var S,e=j(this),k=j(z),T=j(I),A=j("body"),R=e.selector||"",P=(new Date).getTime(),E=[],F=w,O="string"==typeof F,D=[].slice.call(arguments,1),q=z.requestAnimationFrame||z.mozRequestAnimationFrame||z.webkitRequestAnimationFrame||z.msRequestAnimationFrame||function(e){setTimeout(e,0)};return e.each(function(){var n,i,e,o,a,t,r,s,l,c=j.isPlainObject(w)?j.extend(!0,{},j.fn.modal.settings,w):j.extend({},j.fn.modal.settings),u=c.selector,d=c.className,f=c.namespace,m=c.error,g="."+f,p="module-"+f,h=j(this),v=j(c.context),b=h.find(u.close),y=this,x=h.data(p),C=!1;l={initialize:function(){l.verbose("Initializing dimmer",v),l.create.id(),l.create.dimmer(),l.refreshModals(),l.bind.events(),c.observeChanges&&l.observeChanges(),l.instantiate()},instantiate:function(){l.verbose("Storing instance of modal"),x=l,h.data(p,x)},create:{dimmer:function(){var e={debug:c.debug,variation:!c.centered&&"top aligned",dimmerName:"modals"},t=j.extend(!0,e,c.dimmerSettings);j.fn.dimmer!==M?(l.debug("Creating dimmer"),o=v.dimmer(t),c.detachable?(l.verbose("Modal is detachable, moving content into dimmer"),o.dimmer("add content",h)):l.set.undetached(),a=o.dimmer("get dimmer")):l.error(m.dimmer)},id:function(){r=(Math.random().toString(16)+"000000000").substr(2,8),t="."+r,l.verbose("Creating unique id for element",r)}},destroy:function(){l.verbose("Destroying previous modal"),h.removeData(p).off(g),k.off(t),a.off(t),b.off(g),v.dimmer("destroy")},observeChanges:function(){"MutationObserver"in z&&((s=new MutationObserver(function(e){l.debug("DOM tree modified, refreshing"),l.refresh()})).observe(y,{childList:!0,subtree:!0}),l.debug("Setting up mutation observer",s))},refresh:function(){l.remove.scrolling(),l.cacheSizes(),l.can.useFlex()||l.set.modalOffset(),l.set.screenHeight(),l.set.type()},refreshModals:function(){i=h.siblings(u.modal),n=i.add(h)},attachEvents:function(e,t){var n=j(e);t=j.isFunction(l[t])?l[t]:l.toggle,0<n.length?(l.debug("Attaching modal events to element",e,t),n.off(g).on("click"+g,t)):l.error(m.notFound,e)},bind:{events:function(){l.verbose("Attaching events"),h.on("click"+g,u.close,l.event.close).on("click"+g,u.approve,l.event.approve).on("click"+g,u.deny,l.event.deny),k.on("resize"+t,l.event.resize)},scrollLock:function(){o.get(0).addEventListener("touchmove",l.event.preventScroll,{passive:!1})}},unbind:{scrollLock:function(){o.get(0).removeEventListener("touchmove",l.event.preventScroll,{passive:!1})}},get:{id:function(){return(Math.random().toString(16)+"000000000").substr(2,8)}},event:{approve:function(){C||!1===c.onApprove.call(y,j(this))?l.verbose("Approve callback returned false cancelling hide"):(C=!0,l.hide(function(){C=!1}))},preventScroll:function(e){e.preventDefault()},deny:function(){C||!1===c.onDeny.call(y,j(this))?l.verbose("Deny callback returned false cancelling hide"):(C=!0,l.hide(function(){C=!1}))},close:function(){l.hide()},click:function(e){if(c.closable){var t=0<j(e.target).closest(u.modal).length,n=j.contains(I.documentElement,e.target);!t&&n&&l.is.active()&&(l.debug("Dimmer clicked, hiding all modals"),l.remove.clickaway(),c.allowMultiple?l.hide():l.hideAll())}else l.verbose("Dimmer clicked but closable setting is disabled")},debounce:function(e,t){clearTimeout(l.timer),l.timer=setTimeout(e,t)},keyboard:function(e){27==e.which&&(c.closable?(l.debug("Escape key pressed hiding modal"),l.hide()):l.debug("Escape key pressed, but closable is set to false"),e.preventDefault())},resize:function(){o.dimmer("is active")&&(l.is.animating()||l.is.active())&&q(l.refresh)}},toggle:function(){l.is.active()||l.is.animating()?l.hide():l.show()},show:function(e){e=j.isFunction(e)?e:function(){},l.refreshModals(),l.set.dimmerSettings(),l.set.dimmerStyles(),l.showModal(e)},hide:function(e){e=j.isFunction(e)?e:function(){},l.refreshModals(),l.hideModal(e)},showModal:function(e){e=j.isFunction(e)?e:function(){},l.is.animating()||!l.is.active()?(l.showDimmer(),l.cacheSizes(),l.can.useFlex()?l.remove.legacy():(l.set.legacy(),l.set.modalOffset(),l.debug("Using non-flex legacy modal positioning.")),l.set.screenHeight(),l.set.type(),l.set.clickaway(),!c.allowMultiple&&l.others.active()?l.hideOthers(l.showModal):(c.allowMultiple&&c.detachable&&h.detach().appendTo(a),c.onShow.call(y),c.transition&&j.fn.transition!==M&&h.transition("is supported")?(l.debug("Showing modal with css animations"),h.transition({debug:c.debug,animation:c.transition+" in",queue:c.queue,duration:c.duration,useFailSafe:!0,onComplete:function(){c.onVisible.apply(y),c.keyboardShortcuts&&l.add.keyboardShortcuts(),l.save.focus(),l.set.active(),c.autofocus&&l.set.autofocus(),e()}})):l.error(m.noTransition))):l.debug("Modal is already visible")},hideModal:function(e,t){e=j.isFunction(e)?e:function(){},l.debug("Hiding modal"),!1!==c.onHide.call(y,j(this))?(l.is.animating()||l.is.active())&&(c.transition&&j.fn.transition!==M&&h.transition("is supported")?(l.remove.active(),h.transition({debug:c.debug,animation:c.transition+" out",queue:c.queue,duration:c.duration,useFailSafe:!0,onStart:function(){l.others.active()||t||l.hideDimmer(),c.keyboardShortcuts&&l.remove.keyboardShortcuts()},onComplete:function(){c.onHidden.call(y),l.remove.dimmerStyles(),l.restore.focus(),e()}})):l.error(m.noTransition)):l.verbose("Hide callback returned false cancelling hide")},showDimmer:function(){o.dimmer("is animating")||!o.dimmer("is active")?(l.debug("Showing dimmer"),o.dimmer("show")):l.debug("Dimmer already visible")},hideDimmer:function(){o.dimmer("is animating")||o.dimmer("is active")?(l.unbind.scrollLock(),o.dimmer("hide",function(){l.remove.clickaway(),l.remove.screenHeight()})):l.debug("Dimmer is not visible cannot hide")},hideAll:function(e){var t=n.filter("."+d.active+", ."+d.animating);e=j.isFunction(e)?e:function(){},0<t.length&&(l.debug("Hiding all visible modals"),l.hideDimmer(),t.modal("hide modal",e))},hideOthers:function(e){var t=i.filter("."+d.active+", ."+d.animating);e=j.isFunction(e)?e:function(){},0<t.length&&(l.debug("Hiding other modals",i),t.modal("hide modal",e,!0))},others:{active:function(){return 0<i.filter("."+d.active).length},animating:function(){return 0<i.filter("."+d.animating).length}},add:{keyboardShortcuts:function(){l.verbose("Adding keyboard shortcuts"),T.on("keyup"+g,l.event.keyboard)}},save:{focus:function(){0<j(I.activeElement).closest(h).length||(e=j(I.activeElement).blur())}},restore:{focus:function(){e&&0<e.length&&e.focus()}},remove:{active:function(){h.removeClass(d.active)},legacy:function(){h.removeClass(d.legacy)},clickaway:function(){a.off("click"+t)},dimmerStyles:function(){a.removeClass(d.inverted),o.removeClass(d.blurring)},bodyStyle:function(){""===A.attr("style")&&(l.verbose("Removing style attribute"),A.removeAttr("style"))},screenHeight:function(){l.debug("Removing page height"),A.css("height","")},keyboardShortcuts:function(){l.verbose("Removing keyboard shortcuts"),T.off("keyup"+g)},scrolling:function(){o.removeClass(d.scrolling),h.removeClass(d.scrolling)}},cacheSizes:function(){h.addClass(d.loading);var e=h.prop("scrollHeight"),t=h.outerWidth(),n=h.outerHeight();l.cache!==M&&0===n||(l.cache={pageHeight:j(I).outerHeight(),width:t,height:n+c.offset,scrollHeight:e+c.offset,contextHeight:"body"==c.context?j(z).height():o.height()},l.cache.topOffset=-l.cache.height/2),h.removeClass(d.loading),l.debug("Caching modal and container sizes",l.cache)},can:{useFlex:function(){return"auto"==c.useFlex?c.detachable&&!l.is.ie():c.useFlex},fit:function(){var e=l.cache.contextHeight,t=l.cache.contextHeight/2,n=l.cache.topOffset,i=l.cache.scrollHeight,o=l.cache.height,a=c.padding;return o<i?t+n+i+a<e:o+2*a<e}},is:{active:function(){return h.hasClass(d.active)},ie:function(){return!z.ActiveXObject&&"ActiveXObject"in z||"ActiveXObject"in z},animating:function(){return h.transition("is supported")?h.transition("is animating"):h.is(":visible")},scrolling:function(){return o.hasClass(d.scrolling)},modernBrowser:function(){return!(z.ActiveXObject||"ActiveXObject"in z)}},set:{autofocus:function(){var e=h.find("[tabindex], :input").filter(":visible"),t=e.filter("[autofocus]"),n=0<t.length?t.first():e.first();0<n.length&&n.focus()},clickaway:function(){a.on("click"+t,l.event.click)},dimmerSettings:function(){if(j.fn.dimmer!==M){var e={debug:c.debug,dimmerName:"modals",closable:"auto",useFlex:l.can.useFlex(),variation:!c.centered&&"top aligned",duration:{show:c.duration,hide:c.duration}},t=j.extend(!0,e,c.dimmerSettings);c.inverted&&(t.variation=t.variation!==M?t.variation+" inverted":"inverted"),v.dimmer("setting",t)}else l.error(m.dimmer)},dimmerStyles:function(){c.inverted?a.addClass(d.inverted):a.removeClass(d.inverted),c.blurring?o.addClass(d.blurring):o.removeClass(d.blurring)},modalOffset:function(){var e=l.cache.width,t=l.cache.height;h.css({marginTop:c.centered&&l.can.fit()?-t/2:0,marginLeft:-e/2}),l.verbose("Setting modal offset for legacy mode")},screenHeight:function(){l.can.fit()?A.css("height",""):(l.debug("Modal is taller than page content, resizing page height"),A.css("height",l.cache.height+2*c.padding))},active:function(){h.addClass(d.active)},scrolling:function(){o.addClass(d.scrolling),h.addClass(d.scrolling),l.unbind.scrollLock()},legacy:function(){h.addClass(d.legacy)},type:function(){l.can.fit()?(l.verbose("Modal fits on screen"),l.others.active()||l.others.animating()||(l.remove.scrolling(),l.bind.scrollLock())):(l.verbose("Modal cannot fit on screen setting to scrolling"),l.set.scrolling())},undetached:function(){o.addClass(d.undetached)}},setting:function(e,t){if(l.debug("Changing setting",e,t),j.isPlainObject(e))j.extend(!0,c,e);else{if(t===M)return c[e];j.isPlainObject(c[e])?j.extend(!0,c[e],t):c[e]=t}},internal:function(e,t){if(j.isPlainObject(e))j.extend(!0,l,e);else{if(t===M)return l[e];l[e]=t}},debug:function(){!c.silent&&c.debug&&(c.performance?l.performance.log(arguments):(l.debug=Function.prototype.bind.call(console.info,console,c.name+":"),l.debug.apply(console,arguments)))},verbose:function(){!c.silent&&c.verbose&&c.debug&&(c.performance?l.performance.log(arguments):(l.verbose=Function.prototype.bind.call(console.info,console,c.name+":"),l.verbose.apply(console,arguments)))},error:function(){c.silent||(l.error=Function.prototype.bind.call(console.error,console,c.name+":"),l.error.apply(console,arguments))},performance:{log:function(e){var t,n;c.performance&&(n=(t=(new Date).getTime())-(P||t),P=t,E.push({Name:e[0],Arguments:[].slice.call(e,1)||"",Element:y,"Execution Time":n})),clearTimeout(l.performance.timer),l.performance.timer=setTimeout(l.performance.display,500)},display:function(){var e=c.name+":",n=0;P=!1,clearTimeout(l.performance.timer),j.each(E,function(e,t){n+=t["Execution Time"]}),e+=" "+n+"ms",R&&(e+=" '"+R+"'"),(console.group!==M||console.table!==M)&&0<E.length&&(console.groupCollapsed(e),console.table?console.table(E):j.each(E,function(e,t){console.log(t.Name+": "+t["Execution Time"]+"ms")}),console.groupEnd()),E=[]}},invoke:function(i,e,t){var o,a,n,r=x;return e=e||D,t=y||t,"string"==typeof i&&r!==M&&(i=i.split(/[\. ]/),o=i.length-1,j.each(i,function(e,t){var n=e!=o?t+i[e+1].charAt(0).toUpperCase()+i[e+1].slice(1):i;if(j.isPlainObject(r[n])&&e!=o)r=r[n];else{if(r[n]!==M)return a=r[n],!1;if(!j.isPlainObject(r[t])||e==o)return r[t]!==M&&(a=r[t]),!1;r=r[t]}})),j.isFunction(a)?n=a.apply(t,e):a!==M&&(n=a),j.isArray(S)?S.push(n):S!==M?S=[S,n]:n!==M&&(S=n),a}},O?(x===M&&l.initialize(),l.invoke(F)):(x!==M&&x.invoke("destroy"),l.initialize())}),S!==M?S:this},j.fn.modal.settings={name:"Modal",namespace:"modal",useFlex:"auto",offset:0,silent:!1,debug:!1,verbose:!1,performance:!0,observeChanges:!1,allowMultiple:!1,detachable:!0,closable:!0,autofocus:!0,inverted:!1,blurring:!1,centered:!0,dimmerSettings:{closable:!1,useCSS:!0},keyboardShortcuts:!0,context:"body",queue:!1,duration:500,transition:"scale",padding:50,onShow:function(){},onVisible:function(){},onHide:function(){return!0},onHidden:function(){},onApprove:function(){return!0},onDeny:function(){return!0},selector:{close:"> .close",approve:".actions .positive, .actions .approve, .actions .ok",deny:".actions .negative, .actions .deny, .actions .cancel",modal:".ui.modal"},error:{dimmer:"UI Dimmer, a required component is not included in this page",method:"The method you called is not defined.",notFound:"The element you specified could not be found"},className:{active:"active",animating:"animating",blurring:"blurring",inverted:"inverted",legacy:"legacy",loading:"loading",scrolling:"scrolling",undetached:"undetached"}}}(jQuery,window,document),function(y,x,e,C){"use strict";x=void 0!==x&&x.Math==Math?x:"undefined"!=typeof self&&self.Math==Math?self:Function("return this")(),y.fn.nag=function(d){var f,e=y(this),m=e.selector||"",g=(new Date).getTime(),p=[],h=d,v="string"==typeof h,b=[].slice.call(arguments,1);return e.each(function(){var s,i=y.isPlainObject(d)?y.extend(!0,{},y.fn.nag.settings,d):y.extend({},y.fn.nag.settings),e=(i.className,i.selector),l=i.error,t=i.namespace,n="."+t,o=t+"-module",a=y(this),r=(a.find(e.close),i.context?y(i.context):y("body")),c=this,u=a.data(o);x.requestAnimationFrame||x.mozRequestAnimationFrame||x.webkitRequestAnimationFrame||x.msRequestAnimationFrame;s={initialize:function(){s.verbose("Initializing element"),a.on("click"+n,e.close,s.dismiss).data(o,s),i.detachable&&a.parent()[0]!==r[0]&&a.detach().prependTo(r),0<i.displayTime&&setTimeout(s.hide,i.displayTime),s.show()},destroy:function(){s.verbose("Destroying instance"),a.removeData(o).off(n)},show:function(){s.should.show()&&!a.is(":visible")&&(s.debug("Showing nag",i.animation.show),"fade"==i.animation.show?a.fadeIn(i.duration,i.easing):a.slideDown(i.duration,i.easing))},hide:function(){s.debug("Showing nag",i.animation.hide),"fade"==i.animation.show?a.fadeIn(i.duration,i.easing):a.slideUp(i.duration,i.easing)},onHide:function(){s.debug("Removing nag",i.animation.hide),a.remove(),i.onHide&&i.onHide()},dismiss:function(e){i.storageMethod&&s.storage.set(i.key,i.value),s.hide(),e.stopImmediatePropagation(),e.preventDefault()},should:{show:function(){return i.persist?(s.debug("Persistent nag is set, can show nag"),!0):s.storage.get(i.key)!=i.value.toString()?(s.debug("Stored value is not set, can show nag",s.storage.get(i.key)),!0):(s.debug("Stored value is set, cannot show nag",s.storage.get(i.key)),!1)}},get:{storageOptions:function(){var e={};return i.expires&&(e.expires=i.expires),i.domain&&(e.domain=i.domain),i.path&&(e.path=i.path),e}},clear:function(){s.storage.remove(i.key)},storage:{set:function(e,t){var n=s.get.storageOptions();if("localstorage"==i.storageMethod&&x.localStorage!==C)x.localStorage.setItem(e,t),s.debug("Value stored using local storage",e,t);else if("sessionstorage"==i.storageMethod&&x.sessionStorage!==C)x.sessionStorage.setItem(e,t),s.debug("Value stored using session storage",e,t);else{if(y.cookie===C)return void s.error(l.noCookieStorage);y.cookie(e,t,n),s.debug("Value stored using cookie",e,t,n)}},get:function(e,t){var n;return"localstorage"==i.storageMethod&&x.localStorage!==C?n=x.localStorage.getItem(e):"sessionstorage"==i.storageMethod&&x.sessionStorage!==C?n=x.sessionStorage.getItem(e):y.cookie!==C?n=y.cookie(e):s.error(l.noCookieStorage),"undefined"!=n&&"null"!=n&&n!==C&&null!==n||(n=C),n},remove:function(e){var t=s.get.storageOptions();"localstorage"==i.storageMethod&&x.localStorage!==C?x.localStorage.removeItem(e):"sessionstorage"==i.storageMethod&&x.sessionStorage!==C?x.sessionStorage.removeItem(e):y.cookie!==C?y.removeCookie(e,t):s.error(l.noStorage)}},setting:function(e,t){if(s.debug("Changing setting",e,t),y.isPlainObject(e))y.extend(!0,i,e);else{if(t===C)return i[e];y.isPlainObject(i[e])?y.extend(!0,i[e],t):i[e]=t}},internal:function(e,t){if(y.isPlainObject(e))y.extend(!0,s,e);else{if(t===C)return s[e];s[e]=t}},debug:function(){!i.silent&&i.debug&&(i.performance?s.performance.log(arguments):(s.debug=Function.prototype.bind.call(console.info,console,i.name+":"),s.debug.apply(console,arguments)))},verbose:function(){!i.silent&&i.verbose&&i.debug&&(i.performance?s.performance.log(arguments):(s.verbose=Function.prototype.bind.call(console.info,console,i.name+":"),s.verbose.apply(console,arguments)))},error:function(){i.silent||(s.error=Function.prototype.bind.call(console.error,console,i.name+":"),s.error.apply(console,arguments))},performance:{log:function(e){var t,n;i.performance&&(n=(t=(new Date).getTime())-(g||t),g=t,p.push({Name:e[0],Arguments:[].slice.call(e,1)||"",Element:c,"Execution Time":n})),clearTimeout(s.performance.timer),s.performance.timer=setTimeout(s.performance.display,500)},display:function(){var e=i.name+":",n=0;g=!1,clearTimeout(s.performance.timer),y.each(p,function(e,t){n+=t["Execution Time"]}),e+=" "+n+"ms",m&&(e+=" '"+m+"'"),(console.group!==C||console.table!==C)&&0<p.length&&(console.groupCollapsed(e),console.table?console.table(p):y.each(p,function(e,t){console.log(t.Name+": "+t["Execution Time"]+"ms")}),console.groupEnd()),p=[]}},invoke:function(i,e,t){var o,a,n,r=u;return e=e||b,t=c||t,"string"==typeof i&&r!==C&&(i=i.split(/[\. ]/),o=i.length-1,y.each(i,function(e,t){var n=e!=o?t+i[e+1].charAt(0).toUpperCase()+i[e+1].slice(1):i;if(y.isPlainObject(r[n])&&e!=o)r=r[n];else{if(r[n]!==C)return a=r[n],!1;if(!y.isPlainObject(r[t])||e==o)return r[t]!==C?a=r[t]:s.error(l.method,i),!1;r=r[t]}})),y.isFunction(a)?n=a.apply(t,e):a!==C&&(n=a),y.isArray(f)?f.push(n):f!==C?f=[f,n]:n!==C&&(f=n),a}},v?(u===C&&s.initialize(),s.invoke(h)):(u!==C&&u.invoke("destroy"),s.initialize())}),f!==C?f:this},y.fn.nag.settings={name:"Nag",silent:!1,debug:!1,verbose:!1,performance:!0,namespace:"Nag",persist:!1,displayTime:0,animation:{show:"slide",hide:"slide"},context:!1,detachable:!1,expires:30,domain:!1,path:"/",storageMethod:"cookie",key:"nag",value:"dismiss",error:{noCookieStorage:"$.cookie is not included. A storage solution is required.",noStorage:"Neither $.cookie or store is defined. A storage solution is required for storing state",method:"The method you called is not defined."},className:{bottom:"bottom",fixed:"fixed"},selector:{close:".close.icon"},speed:500,easing:"easeOutQuad",onHide:function(){}},y.extend(y.easing,{easeOutQuad:function(e,t,n,i,o){return-i*(t/=o)*(t-2)+n}})}(jQuery,window,document),function(z,I,M,L){"use strict";I=void 0!==I&&I.Math==Math?I:"undefined"!=typeof self&&self.Math==Math?self:Function("return this")(),z.fn.popup=function(k){var T,e=z(this),A=z(M),R=z(I),P=z("body"),E=e.selector||"",F=(new Date).getTime(),O=[],D=k,q="string"==typeof D,j=[].slice.call(arguments,1);return e.each(function(){var u,c,e,t,n,d,f=z.isPlainObject(k)?z.extend(!0,{},z.fn.popup.settings,k):z.extend({},z.fn.popup.settings),o=f.selector,m=f.className,g=f.error,p=f.metadata,i=f.namespace,a="."+f.namespace,r="module-"+i,h=z(this),s=z(f.context),l=z(f.scrollContext),v=z(f.boundary),b=f.target?z(f.target):h,y=0,x=!1,C=!1,w=this,S=h.data(r);d={initialize:function(){d.debug("Initializing",h),d.createID(),d.bind.events(),!d.exists()&&f.preserve&&d.create(),f.observeChanges&&d.observeChanges(),d.instantiate()},instantiate:function(){d.verbose("Storing instance",d),S=d,h.data(r,S)},observeChanges:function(){"MutationObserver"in I&&((e=new MutationObserver(d.event.documentChanged)).observe(M,{childList:!0,subtree:!0}),d.debug("Setting up mutation observer",e))},refresh:function(){f.popup?u=z(f.popup).eq(0):f.inline&&(u=b.nextAll(o.popup).eq(0),f.popup=u),f.popup?(u.addClass(m.loading),c=d.get.offsetParent(),u.removeClass(m.loading),f.movePopup&&d.has.popup()&&d.get.offsetParent(u)[0]!==c[0]&&(d.debug("Moving popup to the same offset parent as target"),u.detach().appendTo(c))):c=f.inline?d.get.offsetParent(b):d.has.popup()?d.get.offsetParent(u):P,c.is("html")&&c[0]!==P[0]&&(d.debug("Setting page as offset parent"),c=P),d.get.variation()&&d.set.variation()},reposition:function(){d.refresh(),d.set.position()},destroy:function(){d.debug("Destroying previous module"),e&&e.disconnect(),u&&!f.preserve&&d.removePopup(),clearTimeout(d.hideTimer),clearTimeout(d.showTimer),d.unbind.close(),d.unbind.events(),h.removeData(r)},event:{start:function(e){var t=z.isPlainObject(f.delay)?f.delay.show:f.delay;clearTimeout(d.hideTimer),C||(d.showTimer=setTimeout(d.show,t))},end:function(){var e=z.isPlainObject(f.delay)?f.delay.hide:f.delay;clearTimeout(d.showTimer),d.hideTimer=setTimeout(d.hide,e)},touchstart:function(e){C=!0,d.show()},resize:function(){d.is.visible()&&d.set.position()},documentChanged:function(e){[].forEach.call(e,function(e){e.removedNodes&&[].forEach.call(e.removedNodes,function(e){(e==w||0<z(e).find(w).length)&&(d.debug("Element removed from DOM, tearing down events"),d.destroy())})})},hideGracefully:function(e){var t=z(e.target),n=z.contains(M.documentElement,e.target),i=0<t.closest(o.popup).length;e&&!i&&n?(d.debug("Click occurred outside popup hiding popup"),d.hide()):d.debug("Click was inside popup, keeping popup open")}},create:function(){var e=d.get.html(),t=d.get.title(),n=d.get.content();e||n||t?(d.debug("Creating pop-up html"),e||(e=f.templates.popup({title:t,content:n})),u=z("<div/>").addClass(m.popup).data(p.activator,h).html(e),f.inline?(d.verbose("Inserting popup element inline",u),u.insertAfter(h)):(d.verbose("Appending popup element to body",u),u.appendTo(s)),d.refresh(),d.set.variation(),f.hoverable&&d.bind.popup(),f.onCreate.call(u,w)):0!==b.next(o.popup).length?(d.verbose("Pre-existing popup found"),f.inline=!0,f.popup=b.next(o.popup).data(p.activator,h),d.refresh(),f.hoverable&&d.bind.popup()):f.popup?(z(f.popup).data(p.activator,h),d.verbose("Used popup specified in settings"),d.refresh(),f.hoverable&&d.bind.popup()):d.debug("No content specified skipping display",w)},createID:function(){n=(Math.random().toString(16)+"000000000").substr(2,8),t="."+n,d.verbose("Creating unique id for element",n)},toggle:function(){d.debug("Toggling pop-up"),d.is.hidden()?(d.debug("Popup is hidden, showing pop-up"),d.unbind.close(),d.show()):(d.debug("Popup is visible, hiding pop-up"),d.hide())},show:function(e){if(e=e||function(){},d.debug("Showing pop-up",f.transition),d.is.hidden()&&(!d.is.active()||!d.is.dropdown())){if(d.exists()||d.create(),!1===f.onShow.call(u,w))return void d.debug("onShow callback returned false, cancelling popup animation");f.preserve||f.popup||d.refresh(),u&&d.set.position()&&(d.save.conditions(),f.exclusive&&d.hideAll(),d.animate.show(e))}},hide:function(e){if(e=e||function(){},d.is.visible()||d.is.animating()){if(!1===f.onHide.call(u,w))return void d.debug("onHide callback returned false, cancelling popup animation");d.remove.visible(),d.unbind.close(),d.restore.conditions(),d.animate.hide(e)}},hideAll:function(){z(o.popup).filter("."+m.popupVisible).each(function(){z(this).data(p.activator).popup("hide")})},exists:function(){return!!u&&(f.inline||f.popup?d.has.popup():1<=u.closest(s).length)},removePopup:function(){d.has.popup()&&!f.popup&&(d.debug("Removing popup",u),u.remove(),u=L,f.onRemove.call(u,w))},save:{conditions:function(){d.cache={title:h.attr("title")},d.cache.title&&h.removeAttr("title"),d.verbose("Saving original attributes",d.cache.title)}},restore:{conditions:function(){return d.cache&&d.cache.title&&(h.attr("title",d.cache.title),d.verbose("Restoring original attributes",d.cache.title)),!0}},supports:{svg:function(){return"undefined"==typeof SVGGraphicsElement}},animate:{show:function(e){e=z.isFunction(e)?e:function(){},f.transition&&z.fn.transition!==L&&h.transition("is supported")?(d.set.visible(),u.transition({animation:f.transition+" in",queue:!1,debug:f.debug,verbose:f.verbose,duration:f.duration,onComplete:function(){d.bind.close(),e.call(u,w),f.onVisible.call(u,w)}})):d.error(g.noTransition)},hide:function(e){e=z.isFunction(e)?e:function(){},d.debug("Hiding pop-up"),!1!==f.onHide.call(u,w)?f.transition&&z.fn.transition!==L&&h.transition("is supported")?u.transition({animation:f.transition+" out",queue:!1,duration:f.duration,debug:f.debug,verbose:f.verbose,onComplete:function(){d.reset(),e.call(u,w),f.onHidden.call(u,w)}}):d.error(g.noTransition):d.debug("onHide callback returned false, cancelling popup animation")}},change:{content:function(e){u.html(e)}},get:{html:function(){return h.removeData(p.html),h.data(p.html)||f.html},title:function(){return h.removeData(p.title),h.data(p.title)||f.title},content:function(){return h.removeData(p.content),h.data(p.content)||f.content||h.attr("title")},variation:function(){return h.removeData(p.variation),h.data(p.variation)||f.variation},popup:function(){return u},popupOffset:function(){return u.offset()},calculations:function(){var e,t=d.get.offsetParent(u),n=b[0],i=v[0]==I,o=f.inline||f.popup&&f.movePopup?b.position():b.offset(),a=i?{top:0,left:0}:v.offset(),r={},s=i?{top:R.scrollTop(),left:R.scrollLeft()}:{top:0,left:0};if(r={target:{element:b[0],width:b.outerWidth(),height:b.outerHeight(),top:o.top,left:o.left,margin:{}},popup:{width:u.outerWidth(),height:u.outerHeight()},parent:{width:c.outerWidth(),height:c.outerHeight()},screen:{top:a.top,left:a.left,scroll:{top:s.top,left:s.left},width:v.width(),height:v.height()}},t.get(0)!==c.get(0)){var l=t.offset();r.target.top-=l.top,r.target.left-=l.left,r.parent.width=t.outerWidth(),r.parent.height=t.outerHeight()}return f.setFluidWidth&&d.is.fluid()&&(r.container={width:u.parent().outerWidth()},r.popup.width=r.container.width),r.target.margin.top=f.inline?parseInt(I.getComputedStyle(n).getPropertyValue("margin-top"),10):0,r.target.margin.left=f.inline?d.is.rtl()?parseInt(I.getComputedStyle(n).getPropertyValue("margin-right"),10):parseInt(I.getComputedStyle(n).getPropertyValue("margin-left"),10):0,e=r.screen,r.boundary={top:e.top+e.scroll.top,bottom:e.top+e.scroll.top+e.height,left:e.left+e.scroll.left,right:e.left+e.scroll.left+e.width},r},id:function(){return n},startEvent:function(){return"hover"==f.on?"mouseenter":"focus"==f.on&&"focus"},scrollEvent:function(){return"scroll"},endEvent:function(){return"hover"==f.on?"mouseleave":"focus"==f.on&&"blur"},distanceFromBoundary:function(e,t){var n,i,o={};return n=(t=t||d.get.calculations()).popup,i=t.boundary,e&&(o={top:e.top-i.top,left:e.left-i.left,right:i.right-(e.left+n.width),bottom:i.bottom-(e.top+n.height)},d.verbose("Distance from boundaries determined",e,o)),o},offsetParent:function(e){var t=(e!==L?e[0]:b[0]).parentNode,n=z(t);if(t)for(var i="none"===n.css("transform"),o="static"===n.css("position"),a=n.is("body");t&&!a&&o&&i;)t=t.parentNode,i="none"===(n=z(t)).css("transform"),o="static"===n.css("position"),a=n.is("body");return n&&0<n.length?n:z()},positions:function(){return{"top left":!1,"top center":!1,"top right":!1,"bottom left":!1,"bottom center":!1,"bottom right":!1,"left center":!1,"right center":!1}},nextPosition:function(e){var t=e.split(" "),n=t[0],i=t[1],o="top"==n||"bottom"==n,a=!1,r=!1,s=!1;return x||(d.verbose("All available positions available"),x=d.get.positions()),d.debug("Recording last position tried",e),x[e]=!0,"opposite"===f.prefer&&(s=(s=[{top:"bottom",bottom:"top",left:"right",right:"left"}[n],i]).join(" "),a=!0===x[s],d.debug("Trying opposite strategy",s)),"adjacent"===f.prefer&&o&&(s=(s=[n,{left:"center",center:"right",right:"left"}[i]]).join(" "),r=!0===x[s],d.debug("Trying adjacent strategy",s)),(r||a)&&(d.debug("Using backup position",s),s={"top left":"top center","top center":"top right","top right":"right center","right center":"bottom right","bottom right":"bottom center","bottom center":"bottom left","bottom left":"left center","left center":"top left"}[e]),s}},set:{position:function(e,t){if(0!==b.length&&0!==u.length){var n,i,o,a,r,s,l,c;if(t=t||d.get.calculations(),e=e||h.data(p.position)||f.position,n=h.data(p.offset)||f.offset,i=f.distanceAway,o=t.target,a=t.popup,r=t.parent,d.should.centerArrow(t)&&(d.verbose("Adjusting offset to center arrow on small target element"),"top left"!=e&&"bottom left"!=e||(n+=o.width/2,n-=f.arrowPixelsFromEdge),"top right"!=e&&"bottom right"!=e||(n-=o.width/2,n+=f.arrowPixelsFromEdge)),0===o.width&&0===o.height&&!d.is.svg(o.element))return d.debug("Popup target is hidden, no action taken"),!1;switch(f.inline&&(d.debug("Adding margin to calculation",o.margin),"left center"==e||"right center"==e?(n+=o.margin.top,i+=-o.margin.left):"top left"==e||"top center"==e||"top right"==e?(n+=o.margin.left,i-=o.margin.top):(n+=o.margin.left,i+=o.margin.top)),d.debug("Determining popup position from calculations",e,t),d.is.rtl()&&(e=e.replace(/left|right/g,function(e){return"left"==e?"right":"left"}),d.debug("RTL: Popup position updated",e)),y==f.maxSearchDepth&&"string"==typeof f.lastResort&&(e=f.lastResort),e){case"top left":s={top:"auto",bottom:r.height-o.top+i,left:o.left+n,right:"auto"};break;case"top center":s={bottom:r.height-o.top+i,left:o.left+o.width/2-a.width/2+n,top:"auto",right:"auto"};break;case"top right":s={bottom:r.height-o.top+i,right:r.width-o.left-o.width-n,top:"auto",left:"auto"};break;case"left center":s={top:o.top+o.height/2-a.height/2+n,right:r.width-o.left+i,left:"auto",bottom:"auto"};break;case"right center":s={top:o.top+o.height/2-a.height/2+n,left:o.left+o.width+i,bottom:"auto",right:"auto"};break;case"bottom left":s={top:o.top+o.height+i,left:o.left+n,bottom:"auto",right:"auto"};break;case"bottom center":s={top:o.top+o.height+i,left:o.left+o.width/2-a.width/2+n,bottom:"auto",right:"auto"};break;case"bottom right":s={top:o.top+o.height+i,right:r.width-o.left-o.width-n,left:"auto",bottom:"auto"}}if(s===L&&d.error(g.invalidPosition,e),d.debug("Calculated popup positioning values",s),u.css(s).removeClass(m.position).addClass(e).addClass(m.loading),l=d.get.popupOffset(),c=d.get.distanceFromBoundary(l,t),d.is.offstage(c,e)){if(d.debug("Position is outside viewport",e),y<f.maxSearchDepth)return y++,e=d.get.nextPosition(e),d.debug("Trying new position",e),!!u&&d.set.position(e,t);if(!f.lastResort)return d.debug("Popup could not find a position to display",u),d.error(g.cannotPlace,w),d.remove.attempts(),d.remove.loading(),d.reset(),f.onUnplaceable.call(u,w),!1;d.debug("No position found, showing with last position")}return d.debug("Position is on stage",e),d.remove.attempts(),d.remove.loading(),f.setFluidWidth&&d.is.fluid()&&d.set.fluidWidth(t),!0}d.error(g.notFound)},fluidWidth:function(e){e=e||d.get.calculations(),d.debug("Automatically setting element width to parent width",e.parent.width),u.css("width",e.container.width)},variation:function(e){(e=e||d.get.variation())&&d.has.popup()&&(d.verbose("Adding variation to popup",e),u.addClass(e))},visible:function(){h.addClass(m.visible)}},remove:{loading:function(){u.removeClass(m.loading)},variation:function(e){(e=e||d.get.variation())&&(d.verbose("Removing variation",e),u.removeClass(e))},visible:function(){h.removeClass(m.visible)},attempts:function(){d.verbose("Resetting all searched positions"),y=0,x=!1}},bind:{events:function(){d.debug("Binding popup events to module"),"click"==f.on&&h.on("click"+a,d.toggle),"hover"==f.on&&h.on("touchstart"+a,d.event.touchstart),d.get.startEvent()&&h.on(d.get.startEvent()+a,d.event.start).on(d.get.endEvent()+a,d.event.end),f.target&&d.debug("Target set to element",b),R.on("resize"+t,d.event.resize)},popup:function(){d.verbose("Allowing hover events on popup to prevent closing"),u&&d.has.popup()&&u.on("mouseenter"+a,d.event.start).on("mouseleave"+a,d.event.end)},close:function(){(!0===f.hideOnScroll||"auto"==f.hideOnScroll&&"click"!=f.on)&&d.bind.closeOnScroll(),d.is.closable()?d.bind.clickaway():"hover"==f.on&&C&&d.bind.touchClose()},closeOnScroll:function(){d.verbose("Binding scroll close event to document"),l.one(d.get.scrollEvent()+t,d.event.hideGracefully)},touchClose:function(){d.verbose("Binding popup touchclose event to document"),A.on("touchstart"+t,function(e){d.verbose("Touched away from popup"),d.event.hideGracefully.call(w,e)})},clickaway:function(){d.verbose("Binding popup close event to document"),A.on("click"+t,function(e){d.verbose("Clicked away from popup"),d.event.hideGracefully.call(w,e)})}},unbind:{events:function(){R.off(t),h.off(a)},close:function(){A.off(t),l.off(t)}},has:{popup:function(){return u&&0<u.length}},should:{centerArrow:function(e){return!d.is.basic()&&e.target.width<=2*f.arrowPixelsFromEdge}},is:{closable:function(){return"auto"==f.closable?"hover"!=f.on:f.closable},offstage:function(e,n){var i=[];return z.each(e,function(e,t){t<-f.jitter&&(d.debug("Position exceeds allowable distance from edge",e,t,n),i.push(e))}),0<i.length},svg:function(e){return d.supports.svg()&&e instanceof SVGGraphicsElement},basic:function(){return h.hasClass(m.basic)},active:function(){return h.hasClass(m.active)},animating:function(){return u!==L&&u.hasClass(m.animating)},fluid:function(){return u!==L&&u.hasClass(m.fluid)},visible:function(){return u!==L&&u.hasClass(m.popupVisible)},dropdown:function(){return h.hasClass(m.dropdown)},hidden:function(){return!d.is.visible()},rtl:function(){return"rtl"==h.css("direction")}},reset:function(){d.remove.visible(),f.preserve?z.fn.transition!==L&&u.transition("remove transition"):d.removePopup()},setting:function(e,t){if(z.isPlainObject(e))z.extend(!0,f,e);else{if(t===L)return f[e];f[e]=t}},internal:function(e,t){if(z.isPlainObject(e))z.extend(!0,d,e);else{if(t===L)return d[e];d[e]=t}},debug:function(){!f.silent&&f.debug&&(f.performance?d.performance.log(arguments):(d.debug=Function.prototype.bind.call(console.info,console,f.name+":"),d.debug.apply(console,arguments)))},verbose:function(){!f.silent&&f.verbose&&f.debug&&(f.performance?d.performance.log(arguments):(d.verbose=Function.prototype.bind.call(console.info,console,f.name+":"),d.verbose.apply(console,arguments)))},error:function(){f.silent||(d.error=Function.prototype.bind.call(console.error,console,f.name+":"),d.error.apply(console,arguments))},performance:{log:function(e){var t,n;f.performance&&(n=(t=(new Date).getTime())-(F||t),F=t,O.push({Name:e[0],Arguments:[].slice.call(e,1)||"",Element:w,"Execution Time":n})),clearTimeout(d.performance.timer),d.performance.timer=setTimeout(d.performance.display,500)},display:function(){var e=f.name+":",n=0;F=!1,clearTimeout(d.performance.timer),z.each(O,function(e,t){n+=t["Execution Time"]}),e+=" "+n+"ms",E&&(e+=" '"+E+"'"),(console.group!==L||console.table!==L)&&0<O.length&&(console.groupCollapsed(e),console.table?console.table(O):z.each(O,function(e,t){console.log(t.Name+": "+t["Execution Time"]+"ms")}),console.groupEnd()),O=[]}},invoke:function(i,e,t){var o,a,n,r=S;return e=e||j,t=w||t,"string"==typeof i&&r!==L&&(i=i.split(/[\. ]/),o=i.length-1,z.each(i,function(e,t){var n=e!=o?t+i[e+1].charAt(0).toUpperCase()+i[e+1].slice(1):i;if(z.isPlainObject(r[n])&&e!=o)r=r[n];else{if(r[n]!==L)return a=r[n],!1;if(!z.isPlainObject(r[t])||e==o)return r[t]!==L&&(a=r[t]),!1;r=r[t]}})),z.isFunction(a)?n=a.apply(t,e):a!==L&&(n=a),z.isArray(T)?T.push(n):T!==L?T=[T,n]:n!==L&&(T=n),a}},q?(S===L&&d.initialize(),d.invoke(D)):(S!==L&&S.invoke("destroy"),d.initialize())}),T!==L?T:this},z.fn.popup.settings={name:"Popup",silent:!1,debug:!1,verbose:!1,performance:!0,namespace:"popup",observeChanges:!0,onCreate:function(){},onRemove:function(){},onShow:function(){},onVisible:function(){},onHide:function(){},onUnplaceable:function(){},onHidden:function(){},on:"hover",boundary:I,addTouchEvents:!0,position:"top left",variation:"",movePopup:!0,target:!1,popup:!1,inline:!1,preserve:!1,hoverable:!1,content:!1,html:!1,title:!1,closable:!0,hideOnScroll:"auto",exclusive:!1,context:"body",scrollContext:I,prefer:"opposite",lastResort:!1,arrowPixelsFromEdge:20,delay:{show:50,hide:70},setFluidWidth:!0,duration:200,transition:"scale",distanceAway:0,jitter:2,offset:0,maxSearchDepth:15,error:{invalidPosition:"The position you specified is not a valid position",cannotPlace:"Popup does not fit within the boundaries of the viewport",method:"The method you called is not defined.",noTransition:"This module requires ui transitions <https://github.com/Semantic-Org/UI-Transition>",notFound:"The target or popup you specified does not exist on the page"},metadata:{activator:"activator",content:"content",html:"html",offset:"offset",position:"position",title:"title",variation:"variation"},className:{active:"active",basic:"basic",animating:"animating",dropdown:"dropdown",fluid:"fluid",loading:"loading",popup:"ui popup",position:"top left center bottom right",visible:"visible",popupVisible:"visible"},selector:{popup:".ui.popup"},templates:{escape:function(e){var t={"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;","'":"&#x27;","`":"&#x60;"};return/[&<>"'`]/.test(e)?e.replace(/[&<>"'`]/g,function(e){return t[e]}):e},popup:function(e){var t="",n=z.fn.popup.settings.templates.escape;return typeof e!==L&&(typeof e.title!==L&&e.title&&(e.title=n(e.title),t+='<div class="header">'+e.title+"</div>"),typeof e.content!==L&&e.content&&(e.content=n(e.content),t+='<div class="content">'+e.content+"</div>")),t}}}}(jQuery,window,document),function(k,e,T,A){"use strict";void 0!==(e=void 0!==e&&e.Math==Math?e:"undefined"!=typeof self&&self.Math==Math?self:Function("return this")())&&e.Math==Math||("undefined"!=typeof self&&self.Math==Math?self:Function("return this")());k.fn.progress=function(h){var v,e=k(this),b=e.selector||"",y=(new Date).getTime(),x=[],C=h,w="string"==typeof C,S=[].slice.call(arguments,1);return e.each(function(){var s,i=k.isPlainObject(h)?k.extend(!0,{},k.fn.progress.settings,h):k.extend({},k.fn.progress.settings),t=i.className,n=i.metadata,e=i.namespace,o=i.selector,l=i.error,a="."+e,r="module-"+e,c=k(this),u=k(this).find(o.bar),d=k(this).find(o.progress),f=k(this).find(o.label),m=this,g=c.data(r),p=!1;s={initialize:function(){s.debug("Initializing progress bar",i),s.set.duration(),s.set.transitionEvent(),s.read.metadata(),s.read.settings(),s.instantiate()},instantiate:function(){s.verbose("Storing instance of progress",s),g=s,c.data(r,s)},destroy:function(){s.verbose("Destroying previous progress for",c),clearInterval(g.interval),s.remove.state(),c.removeData(r),g=A},reset:function(){s.remove.nextValue(),s.update.progress(0)},complete:function(){(s.percent===A||s.percent<100)&&(s.remove.progressPoll(),s.set.percent(100))},read:{metadata:function(){var e={percent:c.data(n.percent),total:c.data(n.total),value:c.data(n.value)};e.percent&&(s.debug("Current percent value set from metadata",e.percent),s.set.percent(e.percent)),e.total&&(s.debug("Total value set from metadata",e.total),s.set.total(e.total)),e.value&&(s.debug("Current value set from metadata",e.value),s.set.value(e.value),s.set.progress(e.value))},settings:function(){!1!==i.total&&(s.debug("Current total set in settings",i.total),s.set.total(i.total)),!1!==i.value&&(s.debug("Current value set in settings",i.value),s.set.value(i.value),s.set.progress(s.value)),!1!==i.percent&&(s.debug("Current percent set in settings",i.percent),s.set.percent(i.percent))}},bind:{transitionEnd:function(t){var e=s.get.transitionEnd();u.one(e+a,function(e){clearTimeout(s.failSafeTimer),t.call(this,e)}),s.failSafeTimer=setTimeout(function(){u.triggerHandler(e)},i.duration+i.failSafeDelay),s.verbose("Adding fail safe timer",s.timer)}},increment:function(e){var t,n;s.has.total()?n=(t=s.get.value())+(e=e||1):(n=(t=s.get.percent())+(e=e||s.get.randomValue()),100,s.debug("Incrementing percentage by",t,n)),n=s.get.normalizedValue(n),s.set.progress(n)},decrement:function(e){var t,n;s.get.total()?(n=(t=s.get.value())-(e=e||1),s.debug("Decrementing value by",e,t)):(n=(t=s.get.percent())-(e=e||s.get.randomValue()),s.debug("Decrementing percentage by",e,t)),n=s.get.normalizedValue(n),s.set.progress(n)},has:{progressPoll:function(){return s.progressPoll},total:function(){return!1!==s.get.total()}},get:{text:function(e){var t=s.value||0,n=s.total||0,i=p?s.get.displayPercent():s.percent||0,o=0<s.total?n-t:100-i;return e=(e=e||"").replace("{value}",t).replace("{total}",n).replace("{left}",o).replace("{percent}",i),s.verbose("Adding variables to progress bar text",e),e},normalizedValue:function(e){if(e<0)return s.debug("Value cannot decrement below 0"),0;if(s.has.total()){if(e>s.total)return s.debug("Value cannot increment above total",s.total),s.total}else if(100<e)return s.debug("Value cannot increment above 100 percent"),100;return e},updateInterval:function(){return"auto"==i.updateInterval?i.duration:i.updateInterval},randomValue:function(){return s.debug("Generating random increment percentage"),Math.floor(Math.random()*i.random.max+i.random.min)},numericValue:function(e){return"string"==typeof e?""!==e.replace(/[^\d.]/g,"")&&+e.replace(/[^\d.]/g,""):e},transitionEnd:function(){var e,t=T.createElement("element"),n={transition:"transitionend",OTransition:"oTransitionEnd",MozTransition:"transitionend",WebkitTransition:"webkitTransitionEnd"};for(e in n)if(t.style[e]!==A)return n[e]},displayPercent:function(){var e=u.width(),t=c.width(),n=parseInt(u.css("min-width"),10)<e?e/t*100:s.percent;return 0<i.precision?Math.round(n*(10*i.precision))/(10*i.precision):Math.round(n)},percent:function(){return s.percent||0},value:function(){return s.nextValue||s.value||0},total:function(){return s.total||!1}},create:{progressPoll:function(){s.progressPoll=setTimeout(function(){s.update.toNextValue(),s.remove.progressPoll()},s.get.updateInterval())}},is:{complete:function(){return s.is.success()||s.is.warning()||s.is.error()},success:function(){return c.hasClass(t.success)},warning:function(){return c.hasClass(t.warning)},error:function(){return c.hasClass(t.error)},active:function(){return c.hasClass(t.active)},visible:function(){return c.is(":visible")}},remove:{progressPoll:function(){s.verbose("Removing progress poll timer"),s.progressPoll&&(clearTimeout(s.progressPoll),delete s.progressPoll)},nextValue:function(){s.verbose("Removing progress value stored for next update"),delete s.nextValue},state:function(){s.verbose("Removing stored state"),delete s.total,delete s.percent,delete s.value},active:function(){s.verbose("Removing active state"),c.removeClass(t.active)},success:function(){s.verbose("Removing success state"),c.removeClass(t.success)},warning:function(){s.verbose("Removing warning state"),c.removeClass(t.warning)},error:function(){s.verbose("Removing error state"),c.removeClass(t.error)}},set:{barWidth:function(e){100<e?s.error(l.tooHigh,e):e<0?s.error(l.tooLow,e):(u.css("width",e+"%"),c.attr("data-percent",parseInt(e,10)))},duration:function(e){e="number"==typeof(e=e||i.duration)?e+"ms":e,s.verbose("Setting progress bar transition duration",e),u.css({"transition-duration":e})},percent:function(e){e="string"==typeof e?+e.replace("%",""):e,e=0<i.precision?Math.round(e*(10*i.precision))/(10*i.precision):Math.round(e),s.percent=e,s.has.total()||(s.value=0<i.precision?Math.round(e/100*s.total*(10*i.precision))/(10*i.precision):Math.round(e/100*s.total*10)/10,i.limitValues&&(s.value=100<s.value?100:s.value<0?0:s.value)),s.set.barWidth(e),s.set.labelInterval(),s.set.labels(),i.onChange.call(m,e,s.value,s.total)},labelInterval:function(){clearInterval(s.interval),s.bind.transitionEnd(function(){s.verbose("Bar finished animating, removing continuous label updates"),clearInterval(s.interval),p=!1,s.set.labels()}),p=!0,s.interval=setInterval(function(){k.contains(T.documentElement,m)||(clearInterval(s.interval),p=!1),s.set.labels()},i.framerate)},labels:function(){s.verbose("Setting both bar progress and outer label text"),s.set.barLabel(),s.set.state()},label:function(e){(e=e||"")&&(e=s.get.text(e),s.verbose("Setting label to text",e),f.text(e))},state:function(e){100===(e=e!==A?e:s.percent)?i.autoSuccess&&!(s.is.warning()||s.is.error()||s.is.success())?(s.set.success(),s.debug("Automatically triggering success at 100%")):(s.verbose("Reached 100% removing active state"),s.remove.active(),s.remove.progressPoll()):0<e?(s.verbose("Adjusting active progress bar label",e),s.set.active()):(s.remove.active(),s.set.label(i.text.active))},barLabel:function(e){e!==A?d.text(s.get.text(e)):"ratio"==i.label&&s.total?(s.verbose("Adding ratio to bar label"),d.text(s.get.text(i.text.ratio))):"percent"==i.label&&(s.verbose("Adding percentage to bar label"),d.text(s.get.text(i.text.percent)))},active:function(e){e=e||i.text.active,s.debug("Setting active state"),i.showActivity&&!s.is.active()&&c.addClass(t.active),s.remove.warning(),s.remove.error(),s.remove.success(),(e=i.onLabelUpdate("active",e,s.value,s.total))&&s.set.label(e),s.bind.transitionEnd(function(){i.onActive.call(m,s.value,s.total)})},success:function(e){e=e||i.text.success||i.text.active,s.debug("Setting success state"),c.addClass(t.success),s.remove.active(),s.remove.warning(),s.remove.error(),s.complete(),e=i.text.success?i.onLabelUpdate("success",e,s.value,s.total):i.onLabelUpdate("active",e,s.value,s.total),s.set.label(e),s.bind.transitionEnd(function(){i.onSuccess.call(m,s.total)})},warning:function(e){e=e||i.text.warning,s.debug("Setting warning state"),c.addClass(t.warning),s.remove.active(),s.remove.success(),s.remove.error(),s.complete(),(e=i.onLabelUpdate("warning",e,s.value,s.total))&&s.set.label(e),s.bind.transitionEnd(function(){i.onWarning.call(m,s.value,s.total)})},error:function(e){e=e||i.text.error,s.debug("Setting error state"),c.addClass(t.error),s.remove.active(),s.remove.success(),s.remove.warning(),s.complete(),(e=i.onLabelUpdate("error",e,s.value,s.total))&&s.set.label(e),s.bind.transitionEnd(function(){i.onError.call(m,s.value,s.total)})},transitionEvent:function(){s.get.transitionEnd()},total:function(e){s.total=e},value:function(e){s.value=e},progress:function(e){s.has.progressPoll()?(s.debug("Updated within interval, setting next update to use new value",e),s.set.nextValue(e)):(s.debug("First update in progress update interval, immediately updating",e),s.update.progress(e),s.create.progressPoll())},nextValue:function(e){s.nextValue=e}},update:{toNextValue:function(){var e=s.nextValue;e&&(s.debug("Update interval complete using last updated value",e),s.update.progress(e),s.remove.nextValue())},progress:function(e){var t;!1===(e=s.get.numericValue(e))&&s.error(l.nonNumeric,e),e=s.get.normalizedValue(e),s.has.total()?(s.set.value(e),t=e/s.total*100,s.debug("Calculating percent complete from total",t)):(t=e,s.debug("Setting value to exact percentage value",t)),s.set.percent(t)}},setting:function(e,t){if(s.debug("Changing setting",e,t),k.isPlainObject(e))k.extend(!0,i,e);else{if(t===A)return i[e];k.isPlainObject(i[e])?k.extend(!0,i[e],t):i[e]=t}},internal:function(e,t){if(k.isPlainObject(e))k.extend(!0,s,e);else{if(t===A)return s[e];s[e]=t}},debug:function(){!i.silent&&i.debug&&(i.performance?s.performance.log(arguments):(s.debug=Function.prototype.bind.call(console.info,console,i.name+":"),s.debug.apply(console,arguments)))},verbose:function(){!i.silent&&i.verbose&&i.debug&&(i.performance?s.performance.log(arguments):(s.verbose=Function.prototype.bind.call(console.info,console,i.name+":"),s.verbose.apply(console,arguments)))},error:function(){i.silent||(s.error=Function.prototype.bind.call(console.error,console,i.name+":"),s.error.apply(console,arguments))},performance:{log:function(e){var t,n;i.performance&&(n=(t=(new Date).getTime())-(y||t),y=t,x.push({Name:e[0],Arguments:[].slice.call(e,1)||"",Element:m,"Execution Time":n})),clearTimeout(s.performance.timer),s.performance.timer=setTimeout(s.performance.display,500)},display:function(){var e=i.name+":",n=0;y=!1,clearTimeout(s.performance.timer),k.each(x,function(e,t){n+=t["Execution Time"]}),e+=" "+n+"ms",b&&(e+=" '"+b+"'"),(console.group!==A||console.table!==A)&&0<x.length&&(console.groupCollapsed(e),console.table?console.table(x):k.each(x,function(e,t){console.log(t.Name+": "+t["Execution Time"]+"ms")}),console.groupEnd()),x=[]}},invoke:function(i,e,t){var o,a,n,r=g;return e=e||S,t=m||t,"string"==typeof i&&r!==A&&(i=i.split(/[\. ]/),o=i.length-1,k.each(i,function(e,t){var n=e!=o?t+i[e+1].charAt(0).toUpperCase()+i[e+1].slice(1):i;if(k.isPlainObject(r[n])&&e!=o)r=r[n];else{if(r[n]!==A)return a=r[n],!1;if(!k.isPlainObject(r[t])||e==o)return r[t]!==A?a=r[t]:s.error(l.method,i),!1;r=r[t]}})),k.isFunction(a)?n=a.apply(t,e):a!==A&&(n=a),k.isArray(v)?v.push(n):v!==A?v=[v,n]:n!==A&&(v=n),a}},w?(g===A&&s.initialize(),s.invoke(C)):(g!==A&&g.invoke("destroy"),s.initialize())}),v!==A?v:this},k.fn.progress.settings={name:"Progress",namespace:"progress",silent:!1,debug:!1,verbose:!1,performance:!0,random:{min:2,max:5},duration:300,updateInterval:"auto",autoSuccess:!0,showActivity:!0,limitValues:!0,label:"percent",precision:0,framerate:1e3/30,percent:!1,total:!1,value:!1,failSafeDelay:100,onLabelUpdate:function(e,t,n,i){return t},onChange:function(e,t,n){},onSuccess:function(e){},onActive:function(e,t){},onError:function(e,t){},onWarning:function(e,t){},error:{method:"The method you called is not defined.",nonNumeric:"Progress value is non numeric",tooHigh:"Value specified is above 100%",tooLow:"Value specified is below 0%"},regExp:{variable:/\{\$*[A-z0-9]+\}/g},metadata:{percent:"percent",total:"total",value:"value"},selector:{bar:"> .bar",label:"> .label",progress:".bar > .progress"},text:{active:!1,error:!1,success:!1,warning:!1,percent:"{percent}%",ratio:"{value} of {total}"},className:{active:"active",error:"error",success:"success",warning:"warning"}}}(jQuery,window,document),function(w,e,t,S){"use strict";e=void 0!==e&&e.Math==Math?e:"undefined"!=typeof self&&self.Math==Math?self:Function("return this")(),w.fn.rating=function(m){var g,p=w(this),h=p.selector||"",v=(new Date).getTime(),b=[],y=m,x="string"==typeof y,C=[].slice.call(arguments,1);return p.each(function(){var e,i,o=w.isPlainObject(m)?w.extend(!0,{},w.fn.rating.settings,m):w.extend({},w.fn.rating.settings),t=o.namespace,a=o.className,n=o.metadata,r=o.selector,s=(o.error,"."+t),l="module-"+t,c=this,u=w(this).data(l),d=w(this),f=d.find(r.icon);i={initialize:function(){i.verbose("Initializing rating module",o),0===f.length&&i.setup.layout(),o.interactive?i.enable():i.disable(),i.set.initialLoad(),i.set.rating(i.get.initialRating()),i.remove.initialLoad(),i.instantiate()},instantiate:function(){i.verbose("Instantiating module",o),u=i,d.data(l,i)},destroy:function(){i.verbose("Destroying previous instance",u),i.remove.events(),d.removeData(l)},refresh:function(){f=d.find(r.icon)},setup:{layout:function(){var e=i.get.maxRating(),t=w.fn.rating.settings.templates.icon(e);i.debug("Generating icon html dynamically"),d.html(t),i.refresh()}},event:{mouseenter:function(){var e=w(this);e.nextAll().removeClass(a.selected),d.addClass(a.selected),e.addClass(a.selected).prevAll().addClass(a.selected)},mouseleave:function(){d.removeClass(a.selected),f.removeClass(a.selected)},click:function(){var e=w(this),t=i.get.rating(),n=f.index(e)+1;("auto"==o.clearable?1===f.length:o.clearable)&&t==n?i.clearRating():i.set.rating(n)}},clearRating:function(){i.debug("Clearing current rating"),i.set.rating(0)},bind:{events:function(){i.verbose("Binding events"),d.on("mouseenter"+s,r.icon,i.event.mouseenter).on("mouseleave"+s,r.icon,i.event.mouseleave).on("click"+s,r.icon,i.event.click)}},remove:{events:function(){i.verbose("Removing events"),d.off(s)},initialLoad:function(){e=!1}},enable:function(){i.debug("Setting rating to interactive mode"),i.bind.events(),d.removeClass(a.disabled)},disable:function(){i.debug("Setting rating to read-only mode"),i.remove.events(),d.addClass(a.disabled)},is:{initialLoad:function(){return e}},get:{initialRating:function(){return d.data(n.rating)!==S?(d.removeData(n.rating),d.data(n.rating)):o.initialRating},maxRating:function(){return d.data(n.maxRating)!==S?(d.removeData(n.maxRating),d.data(n.maxRating)):o.maxRating},rating:function(){var e=f.filter("."+a.active).length;return i.verbose("Current rating retrieved",e),e}},set:{rating:function(e){var t=0<=e-1?e-1:0,n=f.eq(t);d.removeClass(a.selected),f.removeClass(a.selected).removeClass(a.active),0<e&&(i.verbose("Setting current rating to",e),n.prevAll().addBack().addClass(a.active)),i.is.initialLoad()||o.onRate.call(c,e)},initialLoad:function(){e=!0}},setting:function(e,t){if(i.debug("Changing setting",e,t),w.isPlainObject(e))w.extend(!0,o,e);else{if(t===S)return o[e];w.isPlainObject(o[e])?w.extend(!0,o[e],t):o[e]=t}},internal:function(e,t){if(w.isPlainObject(e))w.extend(!0,i,e);else{if(t===S)return i[e];i[e]=t}},debug:function(){!o.silent&&o.debug&&(o.performance?i.performance.log(arguments):(i.debug=Function.prototype.bind.call(console.info,console,o.name+":"),i.debug.apply(console,arguments)))},verbose:function(){!o.silent&&o.verbose&&o.debug&&(o.performance?i.performance.log(arguments):(i.verbose=Function.prototype.bind.call(console.info,console,o.name+":"),i.verbose.apply(console,arguments)))},error:function(){o.silent||(i.error=Function.prototype.bind.call(console.error,console,o.name+":"),i.error.apply(console,arguments))},performance:{log:function(e){var t,n;o.performance&&(n=(t=(new Date).getTime())-(v||t),v=t,b.push({Name:e[0],Arguments:[].slice.call(e,1)||"",Element:c,"Execution Time":n})),clearTimeout(i.performance.timer),i.performance.timer=setTimeout(i.performance.display,500)},display:function(){var e=o.name+":",n=0;v=!1,clearTimeout(i.performance.timer),w.each(b,function(e,t){n+=t["Execution Time"]}),e+=" "+n+"ms",h&&(e+=" '"+h+"'"),1<p.length&&(e+=" ("+p.length+")"),(console.group!==S||console.table!==S)&&0<b.length&&(console.groupCollapsed(e),console.table?console.table(b):w.each(b,function(e,t){console.log(t.Name+": "+t["Execution Time"]+"ms")}),console.groupEnd()),b=[]}},invoke:function(i,e,t){var o,a,n,r=u;return e=e||C,t=c||t,"string"==typeof i&&r!==S&&(i=i.split(/[\. ]/),o=i.length-1,w.each(i,function(e,t){var n=e!=o?t+i[e+1].charAt(0).toUpperCase()+i[e+1].slice(1):i;if(w.isPlainObject(r[n])&&e!=o)r=r[n];else{if(r[n]!==S)return a=r[n],!1;if(!w.isPlainObject(r[t])||e==o)return r[t]!==S&&(a=r[t]),!1;r=r[t]}})),w.isFunction(a)?n=a.apply(t,e):a!==S&&(n=a),w.isArray(g)?g.push(n):g!==S?g=[g,n]:n!==S&&(g=n),a}},x?(u===S&&i.initialize(),i.invoke(y)):(u!==S&&u.invoke("destroy"),i.initialize())}),g!==S?g:this},w.fn.rating.settings={name:"Rating",namespace:"rating",slent:!1,debug:!1,verbose:!1,performance:!0,initialRating:0,interactive:!0,maxRating:4,clearable:"auto",fireOnInit:!1,onRate:function(e){},error:{method:"The method you called is not defined",noMaximum:"No maximum rating specified. Cannot generate HTML automatically"},metadata:{rating:"rating",maxRating:"maxRating"},className:{active:"active",disabled:"disabled",selected:"selected",loading:"loading"},selector:{icon:".icon"},templates:{icon:function(e){for(var t=1,n="";t<=e;)n+='<i class="icon"></i>',t++;return n}}}}(jQuery,window,document),function(E,F,O,D){"use strict";F=void 0!==F&&F.Math==Math?F:"undefined"!=typeof self&&self.Math==Math?self:Function("return this")(),E.fn.search=function(l){var C,w=E(this),S=w.selector||"",k=(new Date).getTime(),T=[],A=l,R="string"==typeof A,P=[].slice.call(arguments,1);return E(this).each(function(){var f,c=E.isPlainObject(l)?E.extend(!0,{},E.fn.search.settings,l):E.extend({},E.fn.search.settings),m=c.className,u=c.metadata,d=c.regExp,a=c.fields,g=c.selector,p=c.error,e=c.namespace,i="."+e,t=e+"-module",h=E(this),v=h.find(g.prompt),n=h.find(g.searchButton),o=h.find(g.results),r=h.find(g.result),b=(h.find(g.category),this),s=h.data(t),y=!1,x=!1;f={initialize:function(){f.verbose("Initializing module"),f.get.settings(),f.determine.searchFields(),f.bind.events(),f.set.type(),f.create.results(),f.instantiate()},instantiate:function(){f.verbose("Storing instance of module",f),s=f,h.data(t,f)},destroy:function(){f.verbose("Destroying instance"),h.off(i).removeData(t)},refresh:function(){f.debug("Refreshing selector cache"),v=h.find(g.prompt),n=h.find(g.searchButton),h.find(g.category),o=h.find(g.results),r=h.find(g.result)},refreshResults:function(){o=h.find(g.results),r=h.find(g.result)},bind:{events:function(){f.verbose("Binding events to search"),c.automatic&&(h.on(f.get.inputEvent()+i,g.prompt,f.event.input),v.attr("autocomplete","off")),h.on("focus"+i,g.prompt,f.event.focus).on("blur"+i,g.prompt,f.event.blur).on("keydown"+i,g.prompt,f.handleKeyboard).on("click"+i,g.searchButton,f.query).on("mousedown"+i,g.results,f.event.result.mousedown).on("mouseup"+i,g.results,f.event.result.mouseup).on("click"+i,g.result,f.event.result.click)}},determine:{searchFields:function(){l&&l.searchFields!==D&&(c.searchFields=l.searchFields)}},event:{input:function(){c.searchDelay?(clearTimeout(f.timer),f.timer=setTimeout(function(){f.is.focused()&&f.query()},c.searchDelay)):f.query()},focus:function(){f.set.focus(),c.searchOnFocus&&f.has.minimumCharacters()&&f.query(function(){f.can.show()&&f.showResults()})},blur:function(e){var t=O.activeElement===this,n=function(){f.cancel.query(),f.remove.focus(),f.timer=setTimeout(f.hideResults,c.hideDelay)};t||(x=!1,f.resultsClicked?(f.debug("Determining if user action caused search to close"),h.one("click.close"+i,g.results,function(e){f.is.inMessage(e)||y?v.focus():(y=!1,f.is.animating()||f.is.hidden()||n())})):(f.debug("Input blurred without user action, closing results"),n()))},result:{mousedown:function(){f.resultsClicked=!0},mouseup:function(){f.resultsClicked=!1},click:function(e){f.debug("Search result selected");var t=E(this),n=t.find(g.title).eq(0),i=t.is("a[href]")?t:t.find("a[href]").eq(0),o=i.attr("href")||!1,a=i.attr("target")||!1,r=(n.html(),0<n.length&&n.text()),s=f.get.results(),l=t.data(u.result)||f.get.result(r,s);if(E.isFunction(c.onSelect)&&!1===c.onSelect.call(b,l,s))return f.debug("Custom onSelect callback cancelled default select action"),void(y=!0);f.hideResults(),r&&f.set.value(r),o&&(f.verbose("Opening search link found in result",i),"_blank"==a||e.ctrlKey?F.open(o):F.location.href=o)}}},handleKeyboard:function(e){var t,n=h.find(g.result),i=h.find(g.category),o=n.filter("."+m.active),a=n.index(o),r=n.length,s=0<o.length,l=e.which,c=13,u=38,d=40;if(l==27&&(f.verbose("Escape key pressed, blurring search field"),f.hideResults(),x=!0),f.is.visible())if(l==c){if(f.verbose("Enter key pressed, selecting active result"),0<n.filter("."+m.active).length)return f.event.result.click.call(n.filter("."+m.active),e),e.preventDefault(),!1}else l==u&&s?(f.verbose("Up key pressed, changing active result"),t=a-1<0?a:a-1,i.removeClass(m.active),n.removeClass(m.active).eq(t).addClass(m.active).closest(i).addClass(m.active),e.preventDefault()):l==d&&(f.verbose("Down key pressed, changing active result"),t=r<=a+1?a:a+1,i.removeClass(m.active),n.removeClass(m.active).eq(t).addClass(m.active).closest(i).addClass(m.active),e.preventDefault());else l==c&&(f.verbose("Enter key pressed, executing query"),f.query(),f.set.buttonPressed(),v.one("keyup",f.remove.buttonFocus))},setup:{api:function(t,n){var e={debug:c.debug,on:!1,cache:c.cache,action:"search",urlData:{query:t},onSuccess:function(e){f.parse.response.call(b,e,t),n()},onFailure:function(){f.displayMessage(p.serverError),n()},onAbort:function(e){},onError:f.error};E.extend(!0,e,c.apiSettings),f.verbose("Setting up API request",e),h.api(e)}},can:{useAPI:function(){return E.fn.api!==D},show:function(){return f.is.focused()&&!f.is.visible()&&!f.is.empty()},transition:function(){return c.transition&&E.fn.transition!==D&&h.transition("is supported")}},is:{animating:function(){return o.hasClass(m.animating)},hidden:function(){return o.hasClass(m.hidden)},inMessage:function(e){if(e.target){var t=E(e.target);return E.contains(O.documentElement,e.target)&&0<t.closest(g.message).length}},empty:function(){return""===o.html()},visible:function(){return 0<o.filter(":visible").length},focused:function(){return 0<v.filter(":focus").length}},get:{settings:function(){E.isPlainObject(l)&&l.searchFullText&&(c.fullTextSearch=l.searchFullText,f.error(c.error.oldSearchSyntax,b))},inputEvent:function(){var e=v[0];return e!==D&&e.oninput!==D?"input":e!==D&&e.onpropertychange!==D?"propertychange":"keyup"},value:function(){return v.val()},results:function(){return h.data(u.results)},result:function(n,e){var i=["title","id"],o=!1;return n=n!==D?n:f.get.value(),e=e!==D?e:f.get.results(),"category"===c.type?(f.debug("Finding result that matches",n),E.each(e,function(e,t){if(E.isArray(t.results)&&(o=f.search.object(n,t.results,i)[0]))return!1})):(f.debug("Finding result in results object",n),o=f.search.object(n,e,i)[0]),o||!1}},select:{firstResult:function(){f.verbose("Selecting first result"),r.first().addClass(m.active)}},set:{focus:function(){h.addClass(m.focus)},loading:function(){h.addClass(m.loading)},value:function(e){f.verbose("Setting search input value",e),v.val(e)},type:function(e){e=e||c.type,"category"==c.type&&h.addClass(c.type)},buttonPressed:function(){n.addClass(m.pressed)}},remove:{loading:function(){h.removeClass(m.loading)},focus:function(){h.removeClass(m.focus)},buttonPressed:function(){n.removeClass(m.pressed)}},query:function(e){e=E.isFunction(e)?e:function(){};var t=f.get.value(),n=f.read.cache(t);e=e||function(){},f.has.minimumCharacters()?(n?(f.debug("Reading result from cache",t),f.save.results(n.results),f.addResults(n.html),f.inject.id(n.results),e()):(f.debug("Querying for",t),E.isPlainObject(c.source)||E.isArray(c.source)?(f.search.local(t),e()):f.can.useAPI()?f.search.remote(t,e):(f.error(p.source),e())),c.onSearchQuery.call(b,t)):f.hideResults()},search:{local:function(e){var t,n=f.search.object(e,c.content);f.set.loading(),f.save.results(n),f.debug("Returned full local search results",n),0<c.maxResults&&(f.debug("Using specified max results",n),n=n.slice(0,c.maxResults)),"category"==c.type&&(n=f.create.categoryResults(n)),t=f.generateResults({results:n}),f.remove.loading(),f.addResults(t),f.inject.id(n),f.write.cache(e,{html:t,results:n})},remote:function(e,t){t=E.isFunction(t)?t:function(){},h.api("is loading")&&h.api("abort"),f.setup.api(e,t),h.api("query")},object:function(i,t,e){var a=[],r=[],s=[],n=i.toString().replace(d.escape,"\\$&"),o=new RegExp(d.beginsWith+n,"i"),l=function(e,t){var n=-1==E.inArray(t,a),i=-1==E.inArray(t,s),o=-1==E.inArray(t,r);n&&i&&o&&e.push(t)};return t=t||c.source,e=e!==D?e:c.searchFields,E.isArray(e)||(e=[e]),t===D||!1===t?(f.error(p.source),[]):(E.each(e,function(e,n){E.each(t,function(e,t){"string"==typeof t[n]&&(-1!==t[n].search(o)?l(a,t):"exact"===c.fullTextSearch&&f.exactSearch(i,t[n])?l(r,t):1==c.fullTextSearch&&f.fuzzySearch(i,t[n])&&l(s,t))})}),E.merge(r,s),E.merge(a,r),a)}},exactSearch:function(e,t){return e=e.toLowerCase(),-1<(t=t.toLowerCase()).indexOf(e)},fuzzySearch:function(e,t){var n=t.length,i=e.length;if("string"!=typeof e)return!1;if(e=e.toLowerCase(),t=t.toLowerCase(),n<i)return!1;if(i===n)return e===t;e:for(var o=0,a=0;o<i;o++){for(var r=e.charCodeAt(o);a<n;)if(t.charCodeAt(a++)===r)continue e;return!1}return!0},parse:{response:function(e,t){var n=f.generateResults(e);f.verbose("Parsing server response",e),e!==D&&t!==D&&e[a.results]!==D&&(f.addResults(n),f.inject.id(e[a.results]),f.write.cache(t,{html:n,results:e[a.results]}),f.save.results(e[a.results]))}},cancel:{query:function(){f.can.useAPI()&&h.api("abort")}},has:{minimumCharacters:function(){return f.get.value().length>=c.minCharacters},results:function(){return 0!==o.length&&""!=o.html()}},clear:{cache:function(e){var t=h.data(u.cache);e?e&&t&&t[e]&&(f.debug("Removing value from cache",e),delete t[e],h.data(u.cache,t)):(f.debug("Clearing cache",e),h.removeData(u.cache))}},read:{cache:function(e){var t=h.data(u.cache);return!!c.cache&&(f.verbose("Checking cache for generated html for query",e),"object"==typeof t&&t[e]!==D&&t[e])}},create:{categoryResults:function(e){var n={};return E.each(e,function(e,t){t.category&&(n[t.category]===D?(f.verbose("Creating new category of results",t.category),n[t.category]={name:t.category,results:[t]}):n[t.category].results.push(t))}),n},id:function(e,t){var n,i=e+1;return t!==D?(n=String.fromCharCode(97+t)+i,f.verbose("Creating category result id",n)):(n=i,f.verbose("Creating result id",n)),n},results:function(){0===o.length&&(o=E("<div />").addClass(m.results).appendTo(h))}},inject:{result:function(e,t,n){f.verbose("Injecting result into results");var i=n!==D?o.children().eq(n).children(g.results).first().children(g.result).eq(t):o.children(g.result).eq(t);f.verbose("Injecting results metadata",i),i.data(u.result,e)},id:function(i){f.debug("Injecting unique ids into results");var o=0,a=0;return"category"===c.type?E.each(i,function(e,i){a=0,E.each(i.results,function(e,t){var n=i.results[e];n.id===D&&(n.id=f.create.id(a,o)),f.inject.result(n,a,o),a++}),o++}):E.each(i,function(e,t){var n=i[e];n.id===D&&(n.id=f.create.id(a)),f.inject.result(n,a),a++}),i}},save:{results:function(e){f.verbose("Saving current search results to metadata",e),h.data(u.results,e)}},write:{cache:function(e,t){var n=h.data(u.cache)!==D?h.data(u.cache):{};c.cache&&(f.verbose("Writing generated html to cache",e,t),n[e]=t,h.data(u.cache,n))}},addResults:function(e){if(E.isFunction(c.onResultsAdd)&&!1===c.onResultsAdd.call(o,e))return f.debug("onResultsAdd callback cancelled default action"),!1;e?(o.html(e),f.refreshResults(),c.selectFirstResult&&f.select.firstResult(),f.showResults()):f.hideResults(function(){o.empty()})},showResults:function(e){e=E.isFunction(e)?e:function(){},x||!f.is.visible()&&f.has.results()&&(f.can.transition()?(f.debug("Showing results with css animations"),o.transition({animation:c.transition+" in",debug:c.debug,verbose:c.verbose,duration:c.duration,onComplete:function(){e()},queue:!0})):(f.debug("Showing results with javascript"),o.stop().fadeIn(c.duration,c.easing)),c.onResultsOpen.call(o))},hideResults:function(e){e=E.isFunction(e)?e:function(){},f.is.visible()&&(f.can.transition()?(f.debug("Hiding results with css animations"),o.transition({animation:c.transition+" out",debug:c.debug,verbose:c.verbose,duration:c.duration,onComplete:function(){e()},queue:!0})):(f.debug("Hiding results with javascript"),o.stop().fadeOut(c.duration,c.easing)),c.onResultsClose.call(o))},generateResults:function(e){f.debug("Generating html from response",e);var t=c.templates[c.type],n=E.isPlainObject(e[a.results])&&!E.isEmptyObject(e[a.results]),i=E.isArray(e[a.results])&&0<e[a.results].length,o="";return n||i?(0<c.maxResults&&(n?"standard"==c.type&&f.error(p.maxResults):e[a.results]=e[a.results].slice(0,c.maxResults)),E.isFunction(t)?o=t(e,a):f.error(p.noTemplate,!1)):c.showNoResults&&(o=f.displayMessage(p.noResults,"empty")),c.onResults.call(b,e),o},displayMessage:function(e,t){return t=t||"standard",f.debug("Displaying message",e,t),f.addResults(c.templates.message(e,t)),c.templates.message(e,t)},setting:function(e,t){if(E.isPlainObject(e))E.extend(!0,c,e);else{if(t===D)return c[e];c[e]=t}},internal:function(e,t){if(E.isPlainObject(e))E.extend(!0,f,e);else{if(t===D)return f[e];f[e]=t}},debug:function(){!c.silent&&c.debug&&(c.performance?f.performance.log(arguments):(f.debug=Function.prototype.bind.call(console.info,console,c.name+":"),f.debug.apply(console,arguments)))},verbose:function(){!c.silent&&c.verbose&&c.debug&&(c.performance?f.performance.log(arguments):(f.verbose=Function.prototype.bind.call(console.info,console,c.name+":"),f.verbose.apply(console,arguments)))},error:function(){c.silent||(f.error=Function.prototype.bind.call(console.error,console,c.name+":"),f.error.apply(console,arguments))},performance:{log:function(e){var t,n;c.performance&&(n=(t=(new Date).getTime())-(k||t),k=t,T.push({Name:e[0],Arguments:[].slice.call(e,1)||"",Element:b,"Execution Time":n})),clearTimeout(f.performance.timer),f.performance.timer=setTimeout(f.performance.display,500)},display:function(){var e=c.name+":",n=0;k=!1,clearTimeout(f.performance.timer),E.each(T,function(e,t){n+=t["Execution Time"]}),e+=" "+n+"ms",S&&(e+=" '"+S+"'"),1<w.length&&(e+=" ("+w.length+")"),(console.group!==D||console.table!==D)&&0<T.length&&(console.groupCollapsed(e),console.table?console.table(T):E.each(T,function(e,t){console.log(t.Name+": "+t["Execution Time"]+"ms")}),console.groupEnd()),T=[]}},invoke:function(i,e,t){var o,a,n,r=s;return e=e||P,t=b||t,"string"==typeof i&&r!==D&&(i=i.split(/[\. ]/),o=i.length-1,E.each(i,function(e,t){var n=e!=o?t+i[e+1].charAt(0).toUpperCase()+i[e+1].slice(1):i;if(E.isPlainObject(r[n])&&e!=o)r=r[n];else{if(r[n]!==D)return a=r[n],!1;if(!E.isPlainObject(r[t])||e==o)return r[t]!==D&&(a=r[t]),!1;r=r[t]}})),E.isFunction(a)?n=a.apply(t,e):a!==D&&(n=a),E.isArray(C)?C.push(n):C!==D?C=[C,n]:n!==D&&(C=n),a}},R?(s===D&&f.initialize(),f.invoke(A)):(s!==D&&s.invoke("destroy"),f.initialize())}),C!==D?C:this},E.fn.search.settings={name:"Search",namespace:"search",silent:!1,debug:!1,verbose:!1,performance:!0,type:"standard",minCharacters:1,selectFirstResult:!1,apiSettings:!1,source:!1,searchOnFocus:!0,searchFields:["title","description"],displayField:"",fullTextSearch:"exact",automatic:!0,hideDelay:0,searchDelay:200,maxResults:7,cache:!0,showNoResults:!0,transition:"scale",duration:200,easing:"easeOutExpo",onSelect:!1,onResultsAdd:!1,onSearchQuery:function(e){},onResults:function(e){},onResultsOpen:function(){},onResultsClose:function(){},className:{animating:"animating",active:"active",empty:"empty",focus:"focus",hidden:"hidden",loading:"loading",results:"results",pressed:"down"},error:{source:"Cannot search. No source used, and Semantic API module was not included",noResults:"Your search returned no results",logging:"Error in debug logging, exiting.",noEndpoint:"No search endpoint was specified",noTemplate:"A valid template name was not specified.",oldSearchSyntax:"searchFullText setting has been renamed fullTextSearch for consistency, please adjust your settings.",serverError:"There was an issue querying the server.",maxResults:"Results must be an array to use maxResults setting",method:"The method you called is not defined."},metadata:{cache:"cache",results:"results",result:"result"},regExp:{escape:/[\-\[\]\/\{\}\(\)\*\+\?\.\\\^\$\|]/g,beginsWith:"(?:s|^)"},fields:{categories:"results",categoryName:"name",categoryResults:"results",description:"description",image:"image",price:"price",results:"results",title:"title",url:"url",action:"action",actionText:"text",actionURL:"url"},selector:{prompt:".prompt",searchButton:".search.button",results:".results",message:".results > .message",category:".category",result:".result",title:".title, .name"},templates:{escape:function(e){var t={"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;","'":"&#x27;","`":"&#x60;"};return/[&<>"'`]/.test(e)?e.replace(/[&<>"'`]/g,function(e){return t[e]}):e},message:function(e,t){var n="";return e!==D&&t!==D&&(n+='<div class="message '+t+'">',n+="empty"==t?'<div class="header">No Results</div class="header"><div class="description">'+e+'</div class="description">':' <div class="description">'+e+"</div>",n+="</div>"),n},category:function(e,n){var i="";E.fn.search.settings.templates.escape;return e[n.categoryResults]!==D&&(E.each(e[n.categoryResults],function(e,t){t[n.results]!==D&&0<t.results.length&&(i+='<div class="category">',t[n.categoryName]!==D&&(i+='<div class="name">'+t[n.categoryName]+"</div>"),i+='<div class="results">',E.each(t.results,function(e,t){t[n.url]?i+='<a class="result" href="'+t[n.url]+'">':i+='<a class="result">',t[n.image]!==D&&(i+='<div class="image"> <img src="'+t[n.image]+'"></div>'),i+='<div class="content">',t[n.price]!==D&&(i+='<div class="price">'+t[n.price]+"</div>"),t[n.title]!==D&&(i+='<div class="title">'+t[n.title]+"</div>"),t[n.description]!==D&&(i+='<div class="description">'+t[n.description]+"</div>"),i+="</div>",i+="</a>"}),i+="</div>",i+="</div>")}),e[n.action]&&(i+='<a href="'+e[n.action][n.actionURL]+'" class="action">'+e[n.action][n.actionText]+"</a>"),i)},standard:function(e,n){var i="";return e[n.results]!==D&&(E.each(e[n.results],function(e,t){t[n.url]?i+='<a class="result" href="'+t[n.url]+'">':i+='<a class="result">',t[n.image]!==D&&(i+='<div class="image"> <img src="'+t[n.image]+'"></div>'),i+='<div class="content">',t[n.price]!==D&&(i+='<div class="price">'+t[n.price]+"</div>"),t[n.title]!==D&&(i+='<div class="title">'+t[n.title]+"</div>"),t[n.description]!==D&&(i+='<div class="description">'+t[n.description]+"</div>"),i+="</div>",i+="</a>"}),e[n.action]&&(i+='<a href="'+e[n.action][n.actionURL]+'" class="action">'+e[n.action][n.actionText]+"</a>"),i)}}}}(jQuery,window,document),function(A,e,R,P){"use strict";e=void 0!==e&&e.Math==Math?e:"undefined"!=typeof self&&self.Math==Math?self:Function("return this")(),A.fn.shape=function(v){var b,y=A(this),x=(A("body"),(new Date).getTime()),C=[],w=v,S="string"==typeof w,k=[].slice.call(arguments,1),T=e.requestAnimationFrame||e.mozRequestAnimationFrame||e.webkitRequestAnimationFrame||e.msRequestAnimationFrame||function(e){setTimeout(e,0)};return y.each(function(){var i,o,a,t=y.selector||"",r=A.isPlainObject(v)?A.extend(!0,{},A.fn.shape.settings,v):A.extend({},A.fn.shape.settings),e=r.namespace,s=r.selector,n=r.error,l=r.className,c="."+e,u="module-"+e,d=A(this),f=d.find(s.sides),m=d.find(s.side),g=!1,p=this,h=d.data(u);a={initialize:function(){a.verbose("Initializing module for",p),a.set.defaultSide(),a.instantiate()},instantiate:function(){a.verbose("Storing instance of module",a),h=a,d.data(u,h)},destroy:function(){a.verbose("Destroying previous module for",p),d.removeData(u).off(c)},refresh:function(){a.verbose("Refreshing selector cache for",p),d=A(p),f=A(this).find(s.shape),m=A(this).find(s.side)},repaint:function(){a.verbose("Forcing repaint event");(f[0]||R.createElement("div")).offsetWidth},animate:function(e,t){a.verbose("Animating box with properties",e),t=t||function(e){a.verbose("Executing animation callback"),e!==P&&e.stopPropagation(),a.reset(),a.set.active()},r.beforeChange.call(o[0]),a.get.transitionEvent()?(a.verbose("Starting CSS animation"),d.addClass(l.animating),f.css(e).one(a.get.transitionEvent(),t),a.set.duration(r.duration),T(function(){d.addClass(l.animating),i.addClass(l.hidden)})):t()},queue:function(e){a.debug("Queueing animation of",e),f.one(a.get.transitionEvent(),function(){a.debug("Executing queued animation"),setTimeout(function(){d.shape(e)},0)})},reset:function(){a.verbose("Animating states reset"),d.removeClass(l.animating).attr("style","").removeAttr("style"),f.attr("style","").removeAttr("style"),m.attr("style","").removeAttr("style").removeClass(l.hidden),o.removeClass(l.animating).attr("style","").removeAttr("style")},is:{complete:function(){return m.filter("."+l.active)[0]==o[0]},animating:function(){return d.hasClass(l.animating)}},set:{defaultSide:function(){i=d.find("."+r.className.active),o=0<i.next(s.side).length?i.next(s.side):d.find(s.side).first(),g=!1,a.verbose("Active side set to",i),a.verbose("Next side set to",o)},duration:function(e){e="number"==typeof(e=e||r.duration)?e+"ms":e,a.verbose("Setting animation duration",e),(r.duration||0===r.duration)&&f.add(m).css({"-webkit-transition-duration":e,"-moz-transition-duration":e,"-ms-transition-duration":e,"-o-transition-duration":e,"transition-duration":e})},currentStageSize:function(){var e=d.find("."+r.className.active),t=e.outerWidth(!0),n=e.outerHeight(!0);d.css({width:t,height:n})},stageSize:function(){var e=d.clone().addClass(l.loading),t=e.find("."+r.className.active),n=g?e.find(s.side).eq(g):0<t.next(s.side).length?t.next(s.side):e.find(s.side).first(),i="next"==r.width?n.outerWidth(!0):"initial"==r.width?d.width():r.width,o="next"==r.height?n.outerHeight(!0):"initial"==r.height?d.height():r.height;t.removeClass(l.active),n.addClass(l.active),e.insertAfter(d),e.remove(),"auto"!=r.width&&(d.css("width",i+r.jitter),a.verbose("Specifying width during animation",i)),"auto"!=r.height&&(d.css("height",o+r.jitter),a.verbose("Specifying height during animation",o))},nextSide:function(e){g=e,o=m.filter(e),g=m.index(o),0===o.length&&(a.set.defaultSide(),a.error(n.side)),a.verbose("Next side manually set to",o)},active:function(){a.verbose("Setting new side to active",o),m.removeClass(l.active),o.addClass(l.active),r.onChange.call(o[0]),a.set.defaultSide()}},flip:{up:function(){if(!a.is.complete()||a.is.animating()||r.allowRepeats)if(a.is.animating())a.queue("flip up");else{a.debug("Flipping up",o);var e=a.get.transform.up();a.set.stageSize(),a.stage.above(),a.animate(e)}else a.debug("Side already visible",o)},down:function(){if(!a.is.complete()||a.is.animating()||r.allowRepeats)if(a.is.animating())a.queue("flip down");else{a.debug("Flipping down",o);var e=a.get.transform.down();a.set.stageSize(),a.stage.below(),a.animate(e)}else a.debug("Side already visible",o)},left:function(){if(!a.is.complete()||a.is.animating()||r.allowRepeats)if(a.is.animating())a.queue("flip left");else{a.debug("Flipping left",o);var e=a.get.transform.left();a.set.stageSize(),a.stage.left(),a.animate(e)}else a.debug("Side already visible",o)},right:function(){if(!a.is.complete()||a.is.animating()||r.allowRepeats)if(a.is.animating())a.queue("flip right");else{a.debug("Flipping right",o);var e=a.get.transform.right();a.set.stageSize(),a.stage.right(),a.animate(e)}else a.debug("Side already visible",o)},over:function(){!a.is.complete()||a.is.animating()||r.allowRepeats?a.is.animating()?a.queue("flip over"):(a.debug("Flipping over",o),a.set.stageSize(),a.stage.behind(),a.animate(a.get.transform.over())):a.debug("Side already visible",o)},back:function(){!a.is.complete()||a.is.animating()||r.allowRepeats?a.is.animating()?a.queue("flip back"):(a.debug("Flipping back",o),a.set.stageSize(),a.stage.behind(),a.animate(a.get.transform.back())):a.debug("Side already visible",o)}},get:{transform:{up:function(){return{transform:"translateY("+-(i.outerHeight(!0)-o.outerHeight(!0))/2+"px) translateZ("+-i.outerHeight(!0)/2+"px) rotateX(-90deg)"}},down:function(){return{transform:"translateY("+-(i.outerHeight(!0)-o.outerHeight(!0))/2+"px) translateZ("+-i.outerHeight(!0)/2+"px) rotateX(90deg)"}},left:function(){return{transform:"translateX("+-(i.outerWidth(!0)-o.outerWidth(!0))/2+"px) translateZ("+-i.outerWidth(!0)/2+"px) rotateY(90deg)"}},right:function(){return{transform:"translateX("+-(i.outerWidth(!0)-o.outerWidth(!0))/2+"px) translateZ("+-i.outerWidth(!0)/2+"px) rotateY(-90deg)"}},over:function(){return{transform:"translateX("+-(i.outerWidth(!0)-o.outerWidth(!0))/2+"px) rotateY(180deg)"}},back:function(){return{transform:"translateX("+-(i.outerWidth(!0)-o.outerWidth(!0))/2+"px) rotateY(-180deg)"}}},transitionEvent:function(){var e,t=R.createElement("element"),n={transition:"transitionend",OTransition:"oTransitionEnd",MozTransition:"transitionend",WebkitTransition:"webkitTransitionEnd"};for(e in n)if(t.style[e]!==P)return n[e]},nextSide:function(){return 0<i.next(s.side).length?i.next(s.side):d.find(s.side).first()}},stage:{above:function(){var e={origin:(i.outerHeight(!0)-o.outerHeight(!0))/2,depth:{active:o.outerHeight(!0)/2,next:i.outerHeight(!0)/2}};a.verbose("Setting the initial animation position as above",o,e),f.css({transform:"translateZ(-"+e.depth.active+"px)"}),i.css({transform:"rotateY(0deg) translateZ("+e.depth.active+"px)"}),o.addClass(l.animating).css({top:e.origin+"px",transform:"rotateX(90deg) translateZ("+e.depth.next+"px)"})},below:function(){var e={origin:(i.outerHeight(!0)-o.outerHeight(!0))/2,depth:{active:o.outerHeight(!0)/2,next:i.outerHeight(!0)/2}};a.verbose("Setting the initial animation position as below",o,e),f.css({transform:"translateZ(-"+e.depth.active+"px)"}),i.css({transform:"rotateY(0deg) translateZ("+e.depth.active+"px)"}),o.addClass(l.animating).css({top:e.origin+"px",transform:"rotateX(-90deg) translateZ("+e.depth.next+"px)"})},left:function(){var e=i.outerWidth(!0),t=o.outerWidth(!0),n={origin:(e-t)/2,depth:{active:t/2,next:e/2}};a.verbose("Setting the initial animation position as left",o,n),f.css({transform:"translateZ(-"+n.depth.active+"px)"}),i.css({transform:"rotateY(0deg) translateZ("+n.depth.active+"px)"}),o.addClass(l.animating).css({left:n.origin+"px",transform:"rotateY(-90deg) translateZ("+n.depth.next+"px)"})},right:function(){var e=i.outerWidth(!0),t=o.outerWidth(!0),n={origin:(e-t)/2,depth:{active:t/2,next:e/2}};a.verbose("Setting the initial animation position as left",o,n),f.css({transform:"translateZ(-"+n.depth.active+"px)"}),i.css({transform:"rotateY(0deg) translateZ("+n.depth.active+"px)"}),o.addClass(l.animating).css({left:n.origin+"px",transform:"rotateY(90deg) translateZ("+n.depth.next+"px)"})},behind:function(){var e=i.outerWidth(!0),t=o.outerWidth(!0),n={origin:(e-t)/2,depth:{active:t/2,next:e/2}};a.verbose("Setting the initial animation position as behind",o,n),i.css({transform:"rotateY(0deg)"}),o.addClass(l.animating).css({left:n.origin+"px",transform:"rotateY(-180deg)"})}},setting:function(e,t){if(a.debug("Changing setting",e,t),A.isPlainObject(e))A.extend(!0,r,e);else{if(t===P)return r[e];A.isPlainObject(r[e])?A.extend(!0,r[e],t):r[e]=t}},internal:function(e,t){if(A.isPlainObject(e))A.extend(!0,a,e);else{if(t===P)return a[e];a[e]=t}},debug:function(){!r.silent&&r.debug&&(r.performance?a.performance.log(arguments):(a.debug=Function.prototype.bind.call(console.info,console,r.name+":"),a.debug.apply(console,arguments)))},verbose:function(){!r.silent&&r.verbose&&r.debug&&(r.performance?a.performance.log(arguments):(a.verbose=Function.prototype.bind.call(console.info,console,r.name+":"),a.verbose.apply(console,arguments)))},error:function(){r.silent||(a.error=Function.prototype.bind.call(console.error,console,r.name+":"),a.error.apply(console,arguments))},performance:{log:function(e){var t,n;r.performance&&(n=(t=(new Date).getTime())-(x||t),x=t,C.push({Name:e[0],Arguments:[].slice.call(e,1)||"",Element:p,"Execution Time":n})),clearTimeout(a.performance.timer),a.performance.timer=setTimeout(a.performance.display,500)},display:function(){var e=r.name+":",n=0;x=!1,clearTimeout(a.performance.timer),A.each(C,function(e,t){n+=t["Execution Time"]}),e+=" "+n+"ms",t&&(e+=" '"+t+"'"),1<y.length&&(e+=" ("+y.length+")"),(console.group!==P||console.table!==P)&&0<C.length&&(console.groupCollapsed(e),console.table?console.table(C):A.each(C,function(e,t){console.log(t.Name+": "+t["Execution Time"]+"ms")}),console.groupEnd()),C=[]}},invoke:function(i,e,t){var o,a,n,r=h;return e=e||k,t=p||t,"string"==typeof i&&r!==P&&(i=i.split(/[\. ]/),o=i.length-1,A.each(i,function(e,t){var n=e!=o?t+i[e+1].charAt(0).toUpperCase()+i[e+1].slice(1):i;if(A.isPlainObject(r[n])&&e!=o)r=r[n];else{if(r[n]!==P)return a=r[n],!1;if(!A.isPlainObject(r[t])||e==o)return r[t]!==P&&(a=r[t]),!1;r=r[t]}})),A.isFunction(a)?n=a.apply(t,e):a!==P&&(n=a),A.isArray(b)?b.push(n):b!==P?b=[b,n]:n!==P&&(b=n),a}},S?(h===P&&a.initialize(),a.invoke(w)):(h!==P&&h.invoke("destroy"),a.initialize())}),b!==P?b:this},A.fn.shape.settings={name:"Shape",silent:!1,debug:!1,verbose:!1,jitter:0,performance:!0,namespace:"shape",width:"initial",height:"initial",beforeChange:function(){},onChange:function(){},allowRepeats:!1,duration:!1,error:{side:"You tried to switch to a side that does not exist.",method:"The method you called is not defined"},className:{animating:"animating",hidden:"hidden",loading:"loading",active:"active"},selector:{sides:".sides",side:".side"}}}(jQuery,window,document),function(q,j,z,I){"use strict";j=void 0!==j&&j.Math==Math?j:"undefined"!=typeof self&&self.Math==Math?self:Function("return this")(),q.fn.sidebar=function(x){var C,e=q(this),w=q(j),S=q(z),k=q("html"),T=q("head"),A=e.selector||"",R=(new Date).getTime(),P=[],E=x,F="string"==typeof E,O=[].slice.call(arguments,1),D=j.requestAnimationFrame||j.mozRequestAnimationFrame||j.webkitRequestAnimationFrame||j.msRequestAnimationFrame||function(e){setTimeout(e,0)};return e.each(function(){var r,s,e,t,l,c,u=q.isPlainObject(x)?q.extend(!0,{},q.fn.sidebar.settings,x):q.extend({},q.fn.sidebar.settings),n=u.selector,a=u.className,i=u.namespace,o=u.regExp,d=u.error,f="."+i,m="module-"+i,g=q(this),p=q(u.context),h=g.children(n.sidebar),v=(p.children(n.fixed),p.children(n.pusher)),b=this,y=g.data(m);c={initialize:function(){c.debug("Initializing sidebar",x),c.create.id(),l=c.get.transitionEvent(),u.delaySetup?D(c.setup.layout):c.setup.layout(),D(function(){c.setup.cache()}),c.instantiate()},instantiate:function(){c.verbose("Storing instance of module",c),y=c,g.data(m,c)},create:{id:function(){e=(Math.random().toString(16)+"000000000").substr(2,8),s="."+e,c.verbose("Creating unique id for element",e)}},destroy:function(){c.verbose("Destroying previous module for",g),g.off(f).removeData(m),c.is.ios()&&c.remove.ios(),p.off(s),w.off(s),S.off(s)},event:{clickaway:function(e){var t=0<v.find(e.target).length||v.is(e.target),n=p.is(e.target);t&&(c.verbose("User clicked on dimmed page"),c.hide()),n&&(c.verbose("User clicked on dimmable context (scaled out page)"),c.hide())},touch:function(e){},containScroll:function(e){b.scrollTop<=0&&(b.scrollTop=1),b.scrollTop+b.offsetHeight>=b.scrollHeight&&(b.scrollTop=b.scrollHeight-b.offsetHeight-1)},scroll:function(e){0===q(e.target).closest(n.sidebar).length&&e.preventDefault()}},bind:{clickaway:function(){c.verbose("Adding clickaway events to context",p),u.closable&&p.on("click"+s,c.event.clickaway).on("touchend"+s,c.event.clickaway)},scrollLock:function(){u.scrollLock&&(c.debug("Disabling page scroll"),w.on("DOMMouseScroll"+s,c.event.scroll)),c.verbose("Adding events to contain sidebar scroll"),S.on("touchmove"+s,c.event.touch),g.on("scroll"+f,c.event.containScroll)}},unbind:{clickaway:function(){c.verbose("Removing clickaway events from context",p),p.off(s)},scrollLock:function(){c.verbose("Removing scroll lock from page"),S.off(s),w.off(s),g.off("scroll"+f)}},add:{inlineCSS:function(){var e,t=c.cache.width||g.outerWidth(),n=c.cache.height||g.outerHeight(),i=c.is.rtl(),o=c.get.direction(),a={left:t,right:-t,top:n,bottom:-n};i&&(c.verbose("RTL detected, flipping widths"),a.left=-t,a.right=t),e="<style>","left"===o||"right"===o?(c.debug("Adding CSS rules for animation distance",t),e+=" .ui.visible."+o+".sidebar ~ .fixed, .ui.visible."+o+".sidebar ~ .pusher {   -webkit-transform: translate3d("+a[o]+"px, 0, 0);           transform: translate3d("+a[o]+"px, 0, 0); }"):"top"!==o&&"bottom"!=o||(e+=" .ui.visible."+o+".sidebar ~ .fixed, .ui.visible."+o+".sidebar ~ .pusher {   -webkit-transform: translate3d(0, "+a[o]+"px, 0);           transform: translate3d(0, "+a[o]+"px, 0); }"),c.is.ie()&&("left"===o||"right"===o?(c.debug("Adding CSS rules for animation distance",t),e+=" body.pushable > .ui.visible."+o+".sidebar ~ .pusher:after {   -webkit-transform: translate3d("+a[o]+"px, 0, 0);           transform: translate3d("+a[o]+"px, 0, 0); }"):"top"!==o&&"bottom"!=o||(e+=" body.pushable > .ui.visible."+o+".sidebar ~ .pusher:after {   -webkit-transform: translate3d(0, "+a[o]+"px, 0);           transform: translate3d(0, "+a[o]+"px, 0); }"),e+=" body.pushable > .ui.visible.left.sidebar ~ .ui.visible.right.sidebar ~ .pusher:after, body.pushable > .ui.visible.right.sidebar ~ .ui.visible.left.sidebar ~ .pusher:after {   -webkit-transform: translate3d(0px, 0, 0);           transform: translate3d(0px, 0, 0); }"),r=q(e+="</style>").appendTo(T),c.debug("Adding sizing css to head",r)}},refresh:function(){c.verbose("Refreshing selector cache"),p=q(u.context),h=p.children(n.sidebar),v=p.children(n.pusher),p.children(n.fixed),c.clear.cache()},refreshSidebars:function(){c.verbose("Refreshing other sidebars"),h=p.children(n.sidebar)},repaint:function(){c.verbose("Forcing repaint event"),b.style.display="none";b.offsetHeight;b.scrollTop=b.scrollTop,b.style.display=""},setup:{cache:function(){c.cache={width:g.outerWidth(),height:g.outerHeight(),rtl:"rtl"==g.css("direction")}},layout:function(){0===p.children(n.pusher).length&&(c.debug("Adding wrapper element for sidebar"),c.error(d.pusher),v=q('<div class="pusher" />'),p.children().not(n.omitted).not(h).wrapAll(v),c.refresh()),0!==g.nextAll(n.pusher).length&&g.nextAll(n.pusher)[0]===v[0]||(c.debug("Moved sidebar to correct parent element"),c.error(d.movedSidebar,b),g.detach().prependTo(p),c.refresh()),c.clear.cache(),c.set.pushable(),c.set.direction()}},attachEvents:function(e,t){var n=q(e);t=q.isFunction(c[t])?c[t]:c.toggle,0<n.length?(c.debug("Attaching sidebar events to element",e,t),n.on("click"+f,t)):c.error(d.notFound,e)},show:function(e){if(e=q.isFunction(e)?e:function(){},c.is.hidden()){if(c.refreshSidebars(),u.overlay&&(c.error(d.overlay),u.transition="overlay"),c.refresh(),c.othersActive())if(c.debug("Other sidebars currently visible"),u.exclusive){if("overlay"!=u.transition)return void c.hideOthers(c.show);c.hideOthers()}else u.transition="overlay";c.pushPage(function(){e.call(b),u.onShow.call(b)}),u.onChange.call(b),u.onVisible.call(b)}else c.debug("Sidebar is already visible")},hide:function(e){e=q.isFunction(e)?e:function(){},(c.is.visible()||c.is.animating())&&(c.debug("Hiding sidebar",e),c.refreshSidebars(),c.pullPage(function(){e.call(b),u.onHidden.call(b)}),u.onChange.call(b),u.onHide.call(b))},othersAnimating:function(){return 0<h.not(g).filter("."+a.animating).length},othersVisible:function(){return 0<h.not(g).filter("."+a.visible).length},othersActive:function(){return c.othersVisible()||c.othersAnimating()},hideOthers:function(e){var t=h.not(g).filter("."+a.visible),n=t.length,i=0;e=e||function(){},t.sidebar("hide",function(){++i==n&&e()})},toggle:function(){c.verbose("Determining toggled direction"),c.is.hidden()?c.show():c.hide()},pushPage:function(t){var e,n,i,o=c.get.transition(),a="overlay"===o||c.othersActive()?g:v;t=q.isFunction(t)?t:function(){},"scale down"==u.transition&&c.scrollToTop(),c.set.transition(o),c.repaint(),e=function(){c.bind.clickaway(),c.add.inlineCSS(),c.set.animating(),c.set.visible()},n=function(){c.set.dimmed()},i=function(e){e.target==a[0]&&(a.off(l+s,i),c.remove.animating(),c.bind.scrollLock(),t.call(b))},a.off(l+s),a.on(l+s,i),D(e),u.dimPage&&!c.othersVisible()&&D(n)},pullPage:function(t){var e,n,i=c.get.transition(),o="overlay"==i||c.othersActive()?g:v;t=q.isFunction(t)?t:function(){},c.verbose("Removing context push state",c.get.direction()),c.unbind.clickaway(),c.unbind.scrollLock(),e=function(){c.set.transition(i),c.set.animating(),c.remove.visible(),u.dimPage&&!c.othersVisible()&&v.removeClass(a.dimmed)},n=function(e){e.target==o[0]&&(o.off(l+s,n),c.remove.animating(),c.remove.transition(),c.remove.inlineCSS(),("scale down"==i||u.returnScroll&&c.is.mobile())&&c.scrollBack(),t.call(b))},o.off(l+s),o.on(l+s,n),D(e)},scrollToTop:function(){c.verbose("Scrolling to top of page to avoid animation issues"),t=q(j).scrollTop(),g.scrollTop(0),j.scrollTo(0,0)},scrollBack:function(){c.verbose("Scrolling back to original page position"),j.scrollTo(0,t)},clear:{cache:function(){c.verbose("Clearing cached dimensions"),c.cache={}}},set:{ios:function(){k.addClass(a.ios)},pushed:function(){p.addClass(a.pushed)},pushable:function(){p.addClass(a.pushable)},dimmed:function(){v.addClass(a.dimmed)},active:function(){g.addClass(a.active)},animating:function(){g.addClass(a.animating)},transition:function(e){e=e||c.get.transition(),g.addClass(e)},direction:function(e){e=e||c.get.direction(),g.addClass(a[e])},visible:function(){g.addClass(a.visible)},overlay:function(){g.addClass(a.overlay)}},remove:{inlineCSS:function(){c.debug("Removing inline css styles",r),r&&0<r.length&&r.remove()},ios:function(){k.removeClass(a.ios)},pushed:function(){p.removeClass(a.pushed)},pushable:function(){p.removeClass(a.pushable)},active:function(){g.removeClass(a.active)},animating:function(){g.removeClass(a.animating)},transition:function(e){e=e||c.get.transition(),g.removeClass(e)},direction:function(e){e=e||c.get.direction(),g.removeClass(a[e])},visible:function(){g.removeClass(a.visible)},overlay:function(){g.removeClass(a.overlay)}},get:{direction:function(){return g.hasClass(a.top)?a.top:g.hasClass(a.right)?a.right:g.hasClass(a.bottom)?a.bottom:a.left},transition:function(){var e,t=c.get.direction();return e=c.is.mobile()?"auto"==u.mobileTransition?u.defaultTransition.mobile[t]:u.mobileTransition:"auto"==u.transition?u.defaultTransition.computer[t]:u.transition,c.verbose("Determined transition",e),e},transitionEvent:function(){var e,t=z.createElement("element"),n={transition:"transitionend",OTransition:"oTransitionEnd",MozTransition:"transitionend",WebkitTransition:"webkitTransitionEnd"};for(e in n)if(t.style[e]!==I)return n[e]}},is:{ie:function(){return!j.ActiveXObject&&"ActiveXObject"in j||"ActiveXObject"in j},ios:function(){var e=navigator.userAgent,t=e.match(o.ios),n=e.match(o.mobileChrome);return!(!t||n)&&(c.verbose("Browser was found to be iOS",e),!0)},mobile:function(){var e=navigator.userAgent;return e.match(o.mobile)?(c.verbose("Browser was found to be mobile",e),!0):(c.verbose("Browser is not mobile, using regular transition",e),!1)},hidden:function(){return!c.is.visible()},visible:function(){return g.hasClass(a.visible)},open:function(){return c.is.visible()},closed:function(){return c.is.hidden()},vertical:function(){return g.hasClass(a.top)},animating:function(){return p.hasClass(a.animating)},rtl:function(){return c.cache.rtl===I&&(c.cache.rtl="rtl"==g.css("direction")),c.cache.rtl}},setting:function(e,t){if(c.debug("Changing setting",e,t),q.isPlainObject(e))q.extend(!0,u,e);else{if(t===I)return u[e];q.isPlainObject(u[e])?q.extend(!0,u[e],t):u[e]=t}},internal:function(e,t){if(q.isPlainObject(e))q.extend(!0,c,e);else{if(t===I)return c[e];c[e]=t}},debug:function(){!u.silent&&u.debug&&(u.performance?c.performance.log(arguments):(c.debug=Function.prototype.bind.call(console.info,console,u.name+":"),c.debug.apply(console,arguments)))},verbose:function(){!u.silent&&u.verbose&&u.debug&&(u.performance?c.performance.log(arguments):(c.verbose=Function.prototype.bind.call(console.info,console,u.name+":"),c.verbose.apply(console,arguments)))},error:function(){u.silent||(c.error=Function.prototype.bind.call(console.error,console,u.name+":"),c.error.apply(console,arguments))},performance:{log:function(e){var t,n;u.performance&&(n=(t=(new Date).getTime())-(R||t),R=t,P.push({Name:e[0],Arguments:[].slice.call(e,1)||"",Element:b,"Execution Time":n})),clearTimeout(c.performance.timer),c.performance.timer=setTimeout(c.performance.display,500)},display:function(){var e=u.name+":",n=0;R=!1,clearTimeout(c.performance.timer),q.each(P,function(e,t){n+=t["Execution Time"]}),e+=" "+n+"ms",A&&(e+=" '"+A+"'"),(console.group!==I||console.table!==I)&&0<P.length&&(console.groupCollapsed(e),console.table?console.table(P):q.each(P,function(e,t){console.log(t.Name+": "+t["Execution Time"]+"ms")}),console.groupEnd()),P=[]}},invoke:function(i,e,t){var o,a,n,r=y;return e=e||O,t=b||t,"string"==typeof i&&r!==I&&(i=i.split(/[\. ]/),o=i.length-1,q.each(i,function(e,t){var n=e!=o?t+i[e+1].charAt(0).toUpperCase()+i[e+1].slice(1):i;if(q.isPlainObject(r[n])&&e!=o)r=r[n];else{if(r[n]!==I)return a=r[n],!1;if(!q.isPlainObject(r[t])||e==o)return r[t]!==I?a=r[t]:c.error(d.method,i),!1;r=r[t]}})),q.isFunction(a)?n=a.apply(t,e):a!==I&&(n=a),q.isArray(C)?C.push(n):C!==I?C=[C,n]:n!==I&&(C=n),a}},F?(y===I&&c.initialize(),c.invoke(E)):(y!==I&&c.invoke("destroy"),c.initialize())}),C!==I?C:this},q.fn.sidebar.settings={name:"Sidebar",namespace:"sidebar",silent:!1,debug:!1,verbose:!1,performance:!0,transition:"auto",mobileTransition:"auto",defaultTransition:{computer:{left:"uncover",right:"uncover",top:"overlay",bottom:"overlay"},mobile:{left:"uncover",right:"uncover",top:"overlay",bottom:"overlay"}},context:"body",exclusive:!1,closable:!0,dimPage:!0,scrollLock:!1,returnScroll:!1,delaySetup:!1,duration:500,onChange:function(){},onShow:function(){},onHide:function(){},onHidden:function(){},onVisible:function(){},className:{active:"active",animating:"animating",dimmed:"dimmed",ios:"ios",pushable:"pushable",pushed:"pushed",right:"right",top:"top",left:"left",bottom:"bottom",visible:"visible"},selector:{fixed:".fixed",omitted:"script, link, style, .ui.modal, .ui.dimmer, .ui.nag, .ui.fixed",pusher:".pusher",sidebar:".ui.sidebar"},regExp:{ios:/(iPad|iPhone|iPod)/g,mobileChrome:/(CriOS)/g,mobile:/Mobile|iP(hone|od|ad)|Android|BlackBerry|IEMobile|Kindle|NetFront|Silk-Accelerated|(hpw|web)OS|Fennec|Minimo|Opera M(obi|ini)|Blazer|Dolfin|Dolphin|Skyfire|Zune/g},error:{method:"The method you called is not defined.",pusher:"Had to add pusher element. For optimal performance make sure body content is inside a pusher element",movedSidebar:"Had to move sidebar. For optimal performance make sure sidebar and pusher are direct children of your body tag",overlay:"The overlay setting is no longer supported, use animation: overlay",notFound:"There were no elements that matched the specified selector"}}}(jQuery,window,document),function(T,A,R,P){"use strict";A=void 0!==A&&A.Math==Math?A:"undefined"!=typeof self&&self.Math==Math?self:Function("return this")(),T.fn.sticky=function(v){var b,e=T(this),y=e.selector||"",x=(new Date).getTime(),C=[],w=v,S="string"==typeof w,k=[].slice.call(arguments,1);return e.each(function(){var i,o,e,t,d,f=T.isPlainObject(v)?T.extend(!0,{},T.fn.sticky.settings,v):T.extend({},T.fn.sticky.settings),n=f.className,a=f.namespace,r=f.error,s="."+a,l="module-"+a,c=T(this),u=T(A),m=T(f.scrollContext),g=(c.selector,c.data(l)),p=A.requestAnimationFrame||A.mozRequestAnimationFrame||A.webkitRequestAnimationFrame||A.msRequestAnimationFrame||function(e){setTimeout(e,0)},h=this;d={initialize:function(){d.determineContainer(),d.determineContext(),d.verbose("Initializing sticky",f,i),d.save.positions(),d.checkErrors(),d.bind.events(),f.observeChanges&&d.observeChanges(),d.instantiate()},instantiate:function(){d.verbose("Storing instance of module",d),g=d,c.data(l,d)},destroy:function(){d.verbose("Destroying previous instance"),d.reset(),e&&e.disconnect(),t&&t.disconnect(),u.off("load"+s,d.event.load).off("resize"+s,d.event.resize),m.off("scrollchange"+s,d.event.scrollchange),c.removeData(l)},observeChanges:function(){"MutationObserver"in A&&(e=new MutationObserver(d.event.documentChanged),t=new MutationObserver(d.event.changed),e.observe(R,{childList:!0,subtree:!0}),t.observe(h,{childList:!0,subtree:!0}),t.observe(o[0],{childList:!0,subtree:!0}),d.debug("Setting up mutation observer",t))},determineContainer:function(){i=f.container?T(f.container):c.offsetParent()},determineContext:function(){0!==(o=f.context?T(f.context):i).length||d.error(r.invalidContext,f.context,c)},checkErrors:function(){if(d.is.hidden()&&d.error(r.visible,c),d.cache.element.height>d.cache.context.height)return d.reset(),void d.error(r.elementSize,c)},bind:{events:function(){u.on("load"+s,d.event.load).on("resize"+s,d.event.resize),m.off("scroll"+s).on("scroll"+s,d.event.scroll).on("scrollchange"+s,d.event.scrollchange)}},event:{changed:function(e){clearTimeout(d.timer),d.timer=setTimeout(function(){d.verbose("DOM tree modified, updating sticky menu",e),d.refresh()},100)},documentChanged:function(e){[].forEach.call(e,function(e){e.removedNodes&&[].forEach.call(e.removedNodes,function(e){(e==h||0<T(e).find(h).length)&&(d.debug("Element removed from DOM, tearing down events"),d.destroy())})})},load:function(){d.verbose("Page contents finished loading"),p(d.refresh)},resize:function(){d.verbose("Window resized"),p(d.refresh)},scroll:function(){p(function(){m.triggerHandler("scrollchange"+s,m.scrollTop())})},scrollchange:function(e,t){d.stick(t),f.onScroll.call(h)}},refresh:function(e){d.reset(),f.context||d.determineContext(),e&&d.determineContainer(),d.save.positions(),d.stick(),f.onReposition.call(h)},supports:{sticky:function(){var e=T("<div/>");e[0];return e.addClass(n.supported),e.css("position").match("sticky")}},save:{lastScroll:function(e){d.lastScroll=e},elementScroll:function(e){d.elementScroll=e},positions:function(){var e={height:m.height()},t={margin:{top:parseInt(c.css("margin-top"),10),bottom:parseInt(c.css("margin-bottom"),10)},offset:c.offset(),width:c.outerWidth(),height:c.outerHeight()},n={offset:o.offset(),height:o.outerHeight()};i.outerHeight();d.is.standardScroll()||(d.debug("Non-standard scroll. Removing scroll offset from element offset"),e.top=m.scrollTop(),e.left=m.scrollLeft(),t.offset.top+=e.top,n.offset.top+=e.top,t.offset.left+=e.left,n.offset.left+=e.left),d.cache={fits:t.height+f.offset<=e.height,sameHeight:t.height==n.height,scrollContext:{height:e.height},element:{margin:t.margin,top:t.offset.top-t.margin.top,left:t.offset.left,width:t.width,height:t.height,bottom:t.offset.top+t.height},context:{top:n.offset.top,height:n.height,bottom:n.offset.top+n.height}},d.set.containerSize(),d.stick(),d.debug("Caching element positions",d.cache)}},get:{direction:function(e){var t="down";return e=e||m.scrollTop(),d.lastScroll!==P&&(d.lastScroll<e?t="down":d.lastScroll>e&&(t="up")),t},scrollChange:function(e){return e=e||m.scrollTop(),d.lastScroll?e-d.lastScroll:0},currentElementScroll:function(){return d.elementScroll?d.elementScroll:d.is.top()?Math.abs(parseInt(c.css("top"),10))||0:Math.abs(parseInt(c.css("bottom"),10))||0},elementScroll:function(e){e=e||m.scrollTop();var t=d.cache.element,n=d.cache.scrollContext,i=d.get.scrollChange(e),o=t.height-n.height+f.offset,a=d.get.currentElementScroll(),r=a+i;return a=d.cache.fits||r<0?0:o<r?o:r}},remove:{lastScroll:function(){delete d.lastScroll},elementScroll:function(e){delete d.elementScroll},minimumSize:function(){i.css("min-height","")},offset:function(){c.css("margin-top","")}},set:{offset:function(){d.verbose("Setting offset on element",f.offset),c.css("margin-top",f.offset)},containerSize:function(){var e=i.get(0).tagName;"HTML"===e||"body"==e?d.determineContainer():Math.abs(i.outerHeight()-d.cache.context.height)>f.jitter&&(d.debug("Context has padding, specifying exact height for container",d.cache.context.height),i.css({height:d.cache.context.height}))},minimumSize:function(){var e=d.cache.element;i.css("min-height",e.height)},scroll:function(e){d.debug("Setting scroll on element",e),d.elementScroll!=e&&(d.is.top()&&c.css("bottom","").css("top",-e),d.is.bottom()&&c.css("top","").css("bottom",e))},size:function(){0!==d.cache.element.height&&0!==d.cache.element.width&&(h.style.setProperty("width",d.cache.element.width+"px","important"),h.style.setProperty("height",d.cache.element.height+"px","important"))}},is:{standardScroll:function(){return m[0]==A},top:function(){return c.hasClass(n.top)},bottom:function(){return c.hasClass(n.bottom)},initialPosition:function(){return!d.is.fixed()&&!d.is.bound()},hidden:function(){return!c.is(":visible")},bound:function(){return c.hasClass(n.bound)},fixed:function(){return c.hasClass(n.fixed)}},stick:function(e){var t=e||m.scrollTop(),n=d.cache,i=n.fits,o=n.sameHeight,a=n.element,r=n.scrollContext,s=n.context,l=d.is.bottom()&&f.pushing?f.bottomOffset:f.offset,c=(e={top:t+l,bottom:t+l+r.height},d.get.direction(e.top),i?0:d.get.elementScroll(e.top)),u=!i;0!==a.height&&!o&&(d.is.initialPosition()?e.top>=s.bottom?(d.debug("Initial element position is bottom of container"),d.bindBottom()):e.top>a.top&&(a.height+e.top-c>=s.bottom?(d.debug("Initial element position is bottom of container"),d.bindBottom()):(d.debug("Initial element position is fixed"),d.fixTop())):d.is.fixed()?d.is.top()?e.top<=a.top?(d.debug("Fixed element reached top of container"),d.setInitialPosition()):a.height+e.top-c>=s.bottom?(d.debug("Fixed element reached bottom of container"),d.bindBottom()):u&&(d.set.scroll(c),d.save.lastScroll(e.top),d.save.elementScroll(c)):d.is.bottom()&&(e.bottom-a.height<=a.top?(d.debug("Bottom fixed rail has reached top of container"),d.setInitialPosition()):e.bottom>=s.bottom?(d.debug("Bottom fixed rail has reached bottom of container"),d.bindBottom()):u&&(d.set.scroll(c),d.save.lastScroll(e.top),d.save.elementScroll(c))):d.is.bottom()&&(e.top<=a.top?(d.debug("Jumped from bottom fixed to top fixed, most likely used home/end button"),d.setInitialPosition()):f.pushing?d.is.bound()&&e.bottom<=s.bottom&&(d.debug("Fixing bottom attached element to bottom of browser."),d.fixBottom()):d.is.bound()&&e.top<=s.bottom-a.height&&(d.debug("Fixing bottom attached element to top of browser."),d.fixTop())))},bindTop:function(){d.debug("Binding element to top of parent container"),d.remove.offset(),c.css({left:"",top:"",marginBottom:""}).removeClass(n.fixed).removeClass(n.bottom).addClass(n.bound).addClass(n.top),f.onTop.call(h),f.onUnstick.call(h)},bindBottom:function(){d.debug("Binding element to bottom of parent container"),d.remove.offset(),c.css({left:"",top:""}).removeClass(n.fixed).removeClass(n.top).addClass(n.bound).addClass(n.bottom),f.onBottom.call(h),f.onUnstick.call(h)},setInitialPosition:function(){d.debug("Returning to initial position"),d.unfix(),d.unbind()},fixTop:function(){d.debug("Fixing element to top of page"),f.setSize&&d.set.size(),d.set.minimumSize(),d.set.offset(),c.css({left:d.cache.element.left,bottom:"",marginBottom:""}).removeClass(n.bound).removeClass(n.bottom).addClass(n.fixed).addClass(n.top),f.onStick.call(h)},fixBottom:function(){d.debug("Sticking element to bottom of page"),f.setSize&&d.set.size(),d.set.minimumSize(),d.set.offset(),c.css({left:d.cache.element.left,bottom:"",marginBottom:""}).removeClass(n.bound).removeClass(n.top).addClass(n.fixed).addClass(n.bottom),f.onStick.call(h)},unbind:function(){d.is.bound()&&(d.debug("Removing container bound position on element"),d.remove.offset(),c.removeClass(n.bound).removeClass(n.top).removeClass(n.bottom))},unfix:function(){d.is.fixed()&&(d.debug("Removing fixed position on element"),d.remove.minimumSize(),d.remove.offset(),c.removeClass(n.fixed).removeClass(n.top).removeClass(n.bottom),f.onUnstick.call(h))},reset:function(){d.debug("Resetting elements position"),d.unbind(),d.unfix(),d.resetCSS(),d.remove.offset(),d.remove.lastScroll()},resetCSS:function(){c.css({width:"",height:""}),i.css({height:""})},setting:function(e,t){if(T.isPlainObject(e))T.extend(!0,f,e);else{if(t===P)return f[e];f[e]=t}},internal:function(e,t){if(T.isPlainObject(e))T.extend(!0,d,e);else{if(t===P)return d[e];d[e]=t}},debug:function(){!f.silent&&f.debug&&(f.performance?d.performance.log(arguments):(d.debug=Function.prototype.bind.call(console.info,console,f.name+":"),d.debug.apply(console,arguments)))},verbose:function(){!f.silent&&f.verbose&&f.debug&&(f.performance?d.performance.log(arguments):(d.verbose=Function.prototype.bind.call(console.info,console,f.name+":"),d.verbose.apply(console,arguments)))},error:function(){f.silent||(d.error=Function.prototype.bind.call(console.error,console,f.name+":"),d.error.apply(console,arguments))},performance:{log:function(e){var t,n;f.performance&&(n=(t=(new Date).getTime())-(x||t),x=t,C.push({Name:e[0],Arguments:[].slice.call(e,1)||"",Element:h,"Execution Time":n})),clearTimeout(d.performance.timer),d.performance.timer=setTimeout(d.performance.display,0)},display:function(){var e=f.name+":",n=0;x=!1,clearTimeout(d.performance.timer),T.each(C,function(e,t){n+=t["Execution Time"]}),e+=" "+n+"ms",y&&(e+=" '"+y+"'"),(console.group!==P||console.table!==P)&&0<C.length&&(console.groupCollapsed(e),console.table?console.table(C):T.each(C,function(e,t){console.log(t.Name+": "+t["Execution Time"]+"ms")}),console.groupEnd()),C=[]}},invoke:function(i,e,t){var o,a,n,r=g;return e=e||k,t=h||t,"string"==typeof i&&r!==P&&(i=i.split(/[\. ]/),o=i.length-1,T.each(i,function(e,t){var n=e!=o?t+i[e+1].charAt(0).toUpperCase()+i[e+1].slice(1):i;if(T.isPlainObject(r[n])&&e!=o)r=r[n];else{if(r[n]!==P)return a=r[n],!1;if(!T.isPlainObject(r[t])||e==o)return r[t]!==P&&(a=r[t]),!1;r=r[t]}})),T.isFunction(a)?n=a.apply(t,e):a!==P&&(n=a),T.isArray(b)?b.push(n):b!==P?b=[b,n]:n!==P&&(b=n),a}},S?(g===P&&d.initialize(),d.invoke(w)):(g!==P&&g.invoke("destroy"),d.initialize())}),b!==P?b:this},T.fn.sticky.settings={name:"Sticky",namespace:"sticky",silent:!1,debug:!1,verbose:!0,performance:!0,pushing:!1,context:!1,container:!1,scrollContext:A,offset:0,bottomOffset:0,jitter:5,setSize:!0,observeChanges:!1,onReposition:function(){},onScroll:function(){},onStick:function(){},onUnstick:function(){},onTop:function(){},onBottom:function(){},error:{container:"Sticky element must be inside a relative container",visible:"Element is hidden, you must call refresh after element becomes visible. Use silent setting to surpress this warning in production.",method:"The method you called is not defined.",invalidContext:"Context specified does not exist",elementSize:"Sticky element is larger than its container, cannot create sticky."},className:{bound:"bound",fixed:"fixed",supported:"native",top:"top",bottom:"bottom"}}}(jQuery,window,document),function(E,F,O,D){"use strict";F=void 0!==F&&F.Math==Math?F:"undefined"!=typeof self&&self.Math==Math?self:Function("return this")(),E.fn.tab=function(r){var c,u=E.isFunction(this)?E(F):E(this),d=u.selector||"",f=(new Date).getTime(),m=[],g=r,A="string"==typeof g,R=[].slice.call(arguments,1),P=!1;return u.each(function(){var p,a,h,v,b,y,x=E.isPlainObject(r)?E.extend(!0,{},E.fn.tab.settings,r):E.extend({},E.fn.tab.settings),C=x.className,w=x.metadata,t=x.selector,S=x.error,e="."+x.namespace,n="module-"+x.namespace,k=E(this),i={},T=!0,o=0,s=this,l=k.data(n);b={initialize:function(){b.debug("Initializing tab menu item",k),b.fix.callbacks(),b.determineTabs(),b.debug("Determining tabs",x.context,a),x.auto&&b.set.auto(),b.bind.events(),x.history&&!P&&(b.initializeHistory(),P=!0),b.instantiate()},instantiate:function(){b.verbose("Storing instance of module",b),l=b,k.data(n,b)},destroy:function(){b.debug("Destroying tabs",k),k.removeData(n).off(e)},bind:{events:function(){E.isWindow(s)||(b.debug("Attaching tab activation events to element",k),k.on("click"+e,b.event.click))}},determineTabs:function(){var e;"parent"===x.context?(0<k.closest(t.ui).length?(e=k.closest(t.ui),b.verbose("Using closest UI element as parent",e)):e=k,p=e.parent(),b.verbose("Determined parent element for creating context",p)):x.context?(p=E(x.context),b.verbose("Using selector for tab context",x.context,p)):p=E("body"),x.childrenOnly?(a=p.children(t.tabs),b.debug("Searching tab context children for tabs",p,a)):(a=p.find(t.tabs),b.debug("Searching tab context for tabs",p,a))},fix:{callbacks:function(){E.isPlainObject(r)&&(r.onTabLoad||r.onTabInit)&&(r.onTabLoad&&(r.onLoad=r.onTabLoad,delete r.onTabLoad,b.error(S.legacyLoad,r.onLoad)),r.onTabInit&&(r.onFirstLoad=r.onTabInit,delete r.onTabInit,b.error(S.legacyInit,r.onFirstLoad)),x=E.extend(!0,{},E.fn.tab.settings,r))}},initializeHistory:function(){if(b.debug("Initializing page state"),E.address===D)return b.error(S.state),!1;if("state"==x.historyType){if(b.debug("Using HTML5 to manage state"),!1===x.path)return b.error(S.path),!1;E.address.history(!0).state(x.path)}E.address.bind("change",b.event.history.change)},event:{click:function(e){var t=E(this).data(w.tab);t!==D?(x.history?(b.verbose("Updating page state",e),E.address.value(t)):(b.verbose("Changing tab",e),b.changeTab(t)),e.preventDefault()):b.debug("No tab specified")},history:{change:function(e){var t=e.pathNames.join("/")||b.get.initialPath(),n=x.templates.determineTitle(t)||!1;b.performance.display(),b.debug("History change event",t,e),y=e,t!==D&&b.changeTab(t),n&&E.address.title(n)}}},refresh:function(){h&&(b.debug("Refreshing tab",h),b.changeTab(h))},cache:{read:function(e){return e!==D&&i[e]},add:function(e,t){e=e||h,b.debug("Adding cached content for",e),i[e]=t},remove:function(e){e=e||h,b.debug("Removing cached content for",e),delete i[e]}},set:{auto:function(){var e="string"==typeof x.path?x.path.replace(/\/$/,"")+"/{$tab}":"/{$tab}";b.verbose("Setting up automatic tab retrieval from server",e),E.isPlainObject(x.apiSettings)?x.apiSettings.url=e:x.apiSettings={url:e}},loading:function(e){var t=b.get.tabElement(e);t.hasClass(C.loading)||(b.verbose("Setting loading state for",t),t.addClass(C.loading).siblings(a).removeClass(C.active+" "+C.loading),0<t.length&&x.onRequest.call(t[0],e))},state:function(e){E.address.value(e)}},changeTab:function(d){var f=F.history&&F.history.pushState&&x.ignoreFirstLoad&&T,m=x.auto||E.isPlainObject(x.apiSettings),g=m&&!f?b.utilities.pathToArray(d):b.get.defaultPathArray(d);d=b.utilities.arrayToPath(g),E.each(g,function(e,t){var n,i,o,a,r=g.slice(0,e+1),s=b.utilities.arrayToPath(r),l=b.is.tab(s),c=e+1==g.length,u=b.get.tabElement(s);if(b.verbose("Looking for tab",t),l){if(b.verbose("Tab was found",t),h=s,v=b.utilities.filterArray(g,r),c?a=!0:(i=g.slice(0,e+2),o=b.utilities.arrayToPath(i),(a=!b.is.tab(o))&&b.verbose("Tab parameters found",i)),a&&m)return f?(b.debug("Ignoring remote content on first tab load",s),T=!1,b.cache.add(d,u.html()),b.activate.all(s),x.onFirstLoad.call(u[0],s,v,y),x.onLoad.call(u[0],s,v,y)):(b.activate.navigation(s),b.fetch.content(s,d)),!1;b.debug("Opened local tab",s),b.activate.all(s),b.cache.read(s)||(b.cache.add(s,!0),b.debug("First time tab loaded calling tab init"),x.onFirstLoad.call(u[0],s,v,y)),x.onLoad.call(u[0],s,v,y)}else{if(-1!=d.search("/")||""===d)return b.error(S.missingTab,k,p,s),!1;if(s=(n=E("#"+d+', a[name="'+d+'"]')).closest("[data-tab]").data(w.tab),u=b.get.tabElement(s),n&&0<n.length&&s)return b.debug("Anchor link used, opening parent tab",u,n),u.hasClass(C.active)||setTimeout(function(){b.scrollTo(n)},0),b.activate.all(s),b.cache.read(s)||(b.cache.add(s,!0),b.debug("First time tab loaded calling tab init"),x.onFirstLoad.call(u[0],s,v,y)),x.onLoad.call(u[0],s,v,y),!1}})},scrollTo:function(e){var t=!!(e&&0<e.length)&&e.offset().top;!1!==t&&(b.debug("Forcing scroll to an in-page link in a hidden tab",t,e),E(O).scrollTop(t))},update:{content:function(e,t,n){var i=b.get.tabElement(e),o=i[0];n=n!==D?n:x.evaluateScripts,"string"==typeof x.cacheType&&"dom"==x.cacheType.toLowerCase()&&"string"!=typeof t?i.empty().append(E(t).clone(!0)):n?(b.debug("Updating HTML and evaluating inline scripts",e,t),i.html(t)):(b.debug("Updating HTML",e,t),o.innerHTML=t)}},fetch:{content:function(t,n){var e,i,o=b.get.tabElement(t),a={dataType:"html",encodeParameters:!1,on:"now",cache:x.alwaysRefresh,headers:{"X-Remote":!0},onSuccess:function(e){"response"==x.cacheType&&b.cache.add(n,e),b.update.content(t,e),t==h?(b.debug("Content loaded",t),b.activate.tab(t)):b.debug("Content loaded in background",t),x.onFirstLoad.call(o[0],t,v,y),x.onLoad.call(o[0],t,v,y),x.loadOnce?b.cache.add(n,!0):"string"==typeof x.cacheType&&"dom"==x.cacheType.toLowerCase()&&0<o.children().length?setTimeout(function(){var e=o.children().clone(!0);e=e.not("script"),b.cache.add(n,e)},0):b.cache.add(n,o.html())},urlData:{tab:n}},r=o.api("get request")||!1,s=r&&"pending"===r.state();n=n||t,i=b.cache.read(n),x.cache&&i?(b.activate.tab(t),b.debug("Adding cached content",n),x.loadOnce||("once"==x.evaluateScripts?b.update.content(t,i,!1):b.update.content(t,i)),x.onLoad.call(o[0],t,v,y)):s?(b.set.loading(t),b.debug("Content is already loading",n)):E.api!==D?(e=E.extend(!0,{},x.apiSettings,a),b.debug("Retrieving remote content",n,e),b.set.loading(t),o.api(e)):b.error(S.api)}},activate:{all:function(e){b.activate.tab(e),b.activate.navigation(e)},tab:function(e){var t=b.get.tabElement(e),n="siblings"==x.deactivate?t.siblings(a):a.not(t),i=t.hasClass(C.active);b.verbose("Showing tab content for",t),i||(t.addClass(C.active),n.removeClass(C.active+" "+C.loading),0<t.length&&x.onVisible.call(t[0],e))},navigation:function(e){var t=b.get.navElement(e),n="siblings"==x.deactivate?t.siblings(u):u.not(t),i=t.hasClass(C.active);b.verbose("Activating tab navigation for",t,e),i||(t.addClass(C.active),n.removeClass(C.active+" "+C.loading))}},deactivate:{all:function(){b.deactivate.navigation(),b.deactivate.tabs()},navigation:function(){u.removeClass(C.active)},tabs:function(){a.removeClass(C.active+" "+C.loading)}},is:{tab:function(e){return e!==D&&0<b.get.tabElement(e).length}},get:{initialPath:function(){return u.eq(0).data(w.tab)||a.eq(0).data(w.tab)},path:function(){return E.address.value()},defaultPathArray:function(e){return b.utilities.pathToArray(b.get.defaultPath(e))},defaultPath:function(e){var t=u.filter("[data-"+w.tab+'^="'+e+'/"]').eq(0).data(w.tab)||!1;if(t){if(b.debug("Found default tab",t),o<x.maxDepth)return o++,b.get.defaultPath(t);b.error(S.recursion)}else b.debug("No default tabs found for",e,a);return o=0,e},navElement:function(e){return e=e||h,u.filter("[data-"+w.tab+'="'+e+'"]')},tabElement:function(e){var t,n,i,o;return e=e||h,i=b.utilities.pathToArray(e),o=b.utilities.last(i),t=a.filter("[data-"+w.tab+'="'+e+'"]'),n=a.filter("[data-"+w.tab+'="'+o+'"]'),0<t.length?t:n},tab:function(){return h}},utilities:{filterArray:function(e,t){return E.grep(e,function(e){return-1==E.inArray(e,t)})},last:function(e){return!!E.isArray(e)&&e[e.length-1]},pathToArray:function(e){return e===D&&(e=h),"string"==typeof e?e.split("/"):[e]},arrayToPath:function(e){return!!E.isArray(e)&&e.join("/")}},setting:function(e,t){if(b.debug("Changing setting",e,t),E.isPlainObject(e))E.extend(!0,x,e);else{if(t===D)return x[e];E.isPlainObject(x[e])?E.extend(!0,x[e],t):x[e]=t}},internal:function(e,t){if(E.isPlainObject(e))E.extend(!0,b,e);else{if(t===D)return b[e];b[e]=t}},debug:function(){!x.silent&&x.debug&&(x.performance?b.performance.log(arguments):(b.debug=Function.prototype.bind.call(console.info,console,x.name+":"),b.debug.apply(console,arguments)))},verbose:function(){!x.silent&&x.verbose&&x.debug&&(x.performance?b.performance.log(arguments):(b.verbose=Function.prototype.bind.call(console.info,console,x.name+":"),b.verbose.apply(console,arguments)))},error:function(){x.silent||(b.error=Function.prototype.bind.call(console.error,console,x.name+":"),b.error.apply(console,arguments))},performance:{log:function(e){var t,n;x.performance&&(n=(t=(new Date).getTime())-(f||t),f=t,m.push({Name:e[0],Arguments:[].slice.call(e,1)||"",Element:s,"Execution Time":n})),clearTimeout(b.performance.timer),b.performance.timer=setTimeout(b.performance.display,500)},display:function(){var e=x.name+":",n=0;f=!1,clearTimeout(b.performance.timer),E.each(m,function(e,t){n+=t["Execution Time"]}),e+=" "+n+"ms",d&&(e+=" '"+d+"'"),(console.group!==D||console.table!==D)&&0<m.length&&(console.groupCollapsed(e),console.table?console.table(m):E.each(m,function(e,t){console.log(t.Name+": "+t["Execution Time"]+"ms")}),console.groupEnd()),m=[]}},invoke:function(i,e,t){var o,a,n,r=l;return e=e||R,t=s||t,"string"==typeof i&&r!==D&&(i=i.split(/[\. ]/),o=i.length-1,E.each(i,function(e,t){var n=e!=o?t+i[e+1].charAt(0).toUpperCase()+i[e+1].slice(1):i;if(E.isPlainObject(r[n])&&e!=o)r=r[n];else{if(r[n]!==D)return a=r[n],!1;if(!E.isPlainObject(r[t])||e==o)return r[t]!==D?a=r[t]:b.error(S.method,i),!1;r=r[t]}})),E.isFunction(a)?n=a.apply(t,e):a!==D&&(n=a),E.isArray(c)?c.push(n):c!==D?c=[c,n]:n!==D&&(c=n),a}},A?(l===D&&b.initialize(),b.invoke(g)):(l!==D&&l.invoke("destroy"),b.initialize())}),c!==D?c:this},E.tab=function(){E(F).tab.apply(this,arguments)},E.fn.tab.settings={name:"Tab",namespace:"tab",silent:!1,debug:!1,verbose:!1,performance:!0,auto:!1,history:!1,historyType:"hash",path:!1,context:!1,childrenOnly:!1,maxDepth:25,deactivate:"siblings",alwaysRefresh:!1,cache:!0,loadOnce:!1,cacheType:"response",ignoreFirstLoad:!1,apiSettings:!1,evaluateScripts:"once",onFirstLoad:function(e,t,n){},onLoad:function(e,t,n){},onVisible:function(e,t,n){},onRequest:function(e,t,n){},templates:{determineTitle:function(e){}},error:{api:"You attempted to load content without API module",method:"The method you called is not defined",missingTab:"Activated tab cannot be found. Tabs are case-sensitive.",noContent:"The tab you specified is missing a content url.",path:"History enabled, but no path was specified",recursion:"Max recursive depth reached",legacyInit:"onTabInit has been renamed to onFirstLoad in 2.0, please adjust your code.",legacyLoad:"onTabLoad has been renamed to onLoad in 2.0. Please adjust your code",state:"History requires Asual's Address library <https://github.com/asual/jquery-address>"},metadata:{tab:"tab",loaded:"loaded",promise:"promise"},className:{loading:"loading",active:"active"},selector:{tabs:".ui.tab",ui:".ui"}}}(jQuery,window,document),function(C,e,w,S){"use strict";e=void 0!==e&&e.Math==Math?e:"undefined"!=typeof self&&self.Math==Math?self:Function("return this")(),C.fn.transition=function(){var c,r=C(this),g=r.selector||"",p=(new Date).getTime(),h=[],v=arguments,b=v[0],y=[].slice.call(arguments,1),x="string"==typeof b;e.requestAnimationFrame||e.mozRequestAnimationFrame||e.webkitRequestAnimationFrame||e.msRequestAnimationFrame;return r.each(function(i){var u,s,t,d,n,o,e,a,f,m=C(this),l=this;(f={initialize:function(){u=f.get.settings.apply(l,v),d=u.className,t=u.error,n=u.metadata,a="."+u.namespace,e="module-"+u.namespace,s=m.data(e)||f,o=f.get.animationEndEvent(),x&&(x=f.invoke(b)),!1===x&&(f.verbose("Converted arguments into settings object",u),u.interval?f.delay(u.animate):f.animate(),f.instantiate())},instantiate:function(){f.verbose("Storing instance of module",f),s=f,m.data(e,s)},destroy:function(){f.verbose("Destroying previous module for",l),m.removeData(e)},refresh:function(){f.verbose("Refreshing display type on next animation"),delete f.displayType},forceRepaint:function(){f.verbose("Forcing element repaint");var e=m.parent(),t=m.next();0===t.length?m.detach().appendTo(e):m.detach().insertBefore(t)},repaint:function(){f.verbose("Repainting element");l.offsetWidth},delay:function(e){var t,n=f.get.animationDirection();n||(n=f.can.transition()?f.get.direction():"static"),e=e!==S?e:u.interval,t="auto"==u.reverse&&n==d.outward||1==u.reverse?(r.length-i)*u.interval:i*u.interval,f.debug("Delaying animation by",t),setTimeout(f.animate,t)},animate:function(e){if(u=e||u,!f.is.supported())return f.error(t.support),!1;if(f.debug("Preparing animation",u.animation),f.is.animating()){if(u.queue)return!u.allowRepeats&&f.has.direction()&&f.is.occurring()&&!0!==f.queuing?f.debug("Animation is currently occurring, preventing queueing same animation",u.animation):f.queue(u.animation),!1;if(!u.allowRepeats&&f.is.occurring())return f.debug("Animation is already occurring, will not execute repeated animation",u.animation),!1;f.debug("New animation started, completing previous early",u.animation),s.complete()}f.can.animate()?f.set.animating(u.animation):f.error(t.noAnimation,u.animation,l)},reset:function(){f.debug("Resetting animation to beginning conditions"),f.remove.animationCallbacks(),f.restore.conditions(),f.remove.animating()},queue:function(e){f.debug("Queueing animation of",e),f.queuing=!0,m.one(o+".queue"+a,function(){f.queuing=!1,f.repaint(),f.animate.apply(this,u)})},complete:function(e){f.debug("Animation complete",u.animation),f.remove.completeCallback(),f.remove.failSafe(),f.is.looping()||(f.is.outward()?(f.verbose("Animation is outward, hiding element"),f.restore.conditions(),f.hide()):f.is.inward()?(f.verbose("Animation is outward, showing element"),f.restore.conditions(),f.show()):(f.verbose("Static animation completed"),f.restore.conditions(),u.onComplete.call(l)))},force:{visible:function(){var e=m.attr("style"),t=f.get.userStyle(),n=f.get.displayType(),i=t+"display: "+n+" !important;",o=m.css("display"),a=e===S||""===e;o!==n?(f.verbose("Overriding default display to show element",n),m.attr("style",i)):a&&m.removeAttr("style")},hidden:function(){var e=m.attr("style"),t=m.css("display"),n=e===S||""===e;"none"===t||f.is.hidden()?n&&m.removeAttr("style"):(f.verbose("Overriding default display to hide element"),m.css("display","none"))}},has:{direction:function(e){var n=!1;return"string"==typeof(e=e||u.animation)&&(e=e.split(" "),C.each(e,function(e,t){t!==d.inward&&t!==d.outward||(n=!0)})),n},inlineDisplay:function(){var e=m.attr("style")||"";return C.isArray(e.match(/display.*?;/,""))}},set:{animating:function(e){var t;f.remove.completeCallback(),e=e||u.animation,t=f.get.animationClass(e),f.save.animation(t),f.force.visible(),f.remove.hidden(),f.remove.direction(),f.start.animation(t)},duration:function(e,t){((t="number"==typeof(t=t||u.duration)?t+"ms":t)||0===t)&&(f.verbose("Setting animation duration",t),m.css({"animation-duration":t}))},direction:function(e){(e=e||f.get.direction())==d.inward?f.set.inward():f.set.outward()},looping:function(){f.debug("Transition set to loop"),m.addClass(d.looping)},hidden:function(){m.addClass(d.transition).addClass(d.hidden)},inward:function(){f.debug("Setting direction to inward"),m.removeClass(d.outward).addClass(d.inward)},outward:function(){f.debug("Setting direction to outward"),m.removeClass(d.inward).addClass(d.outward)},visible:function(){m.addClass(d.transition).addClass(d.visible)}},start:{animation:function(e){e=e||f.get.animationClass(),f.debug("Starting tween",e),m.addClass(e).one(o+".complete"+a,f.complete),u.useFailSafe&&f.add.failSafe(),f.set.duration(u.duration),u.onStart.call(l)}},save:{animation:function(e){f.cache||(f.cache={}),f.cache.animation=e},displayType:function(e){"none"!==e&&m.data(n.displayType,e)},transitionExists:function(e,t){C.fn.transition.exists[e]=t,f.verbose("Saving existence of transition",e,t)}},restore:{conditions:function(){var e=f.get.currentAnimation();e&&(m.removeClass(e),f.verbose("Removing animation class",f.cache)),f.remove.duration()}},add:{failSafe:function(){var e=f.get.duration();f.timer=setTimeout(function(){m.triggerHandler(o)},e+u.failSafeDelay),f.verbose("Adding fail safe timer",f.timer)}},remove:{animating:function(){m.removeClass(d.animating)},animationCallbacks:function(){f.remove.queueCallback(),f.remove.completeCallback()},queueCallback:function(){m.off(".queue"+a)},completeCallback:function(){m.off(".complete"+a)},display:function(){m.css("display","")},direction:function(){m.removeClass(d.inward).removeClass(d.outward)},duration:function(){m.css("animation-duration","")},failSafe:function(){f.verbose("Removing fail safe timer",f.timer),f.timer&&clearTimeout(f.timer)},hidden:function(){m.removeClass(d.hidden)},visible:function(){m.removeClass(d.visible)},looping:function(){f.debug("Transitions are no longer looping"),f.is.looping()&&(f.reset(),m.removeClass(d.looping))},transition:function(){m.removeClass(d.visible).removeClass(d.hidden)}},get:{settings:function(e,t,n){return"object"==typeof e?C.extend(!0,{},C.fn.transition.settings,e):"function"==typeof n?C.extend({},C.fn.transition.settings,{animation:e,onComplete:n,duration:t}):"string"==typeof t||"number"==typeof t?C.extend({},C.fn.transition.settings,{animation:e,duration:t}):"object"==typeof t?C.extend({},C.fn.transition.settings,t,{animation:e}):"function"==typeof t?C.extend({},C.fn.transition.settings,{animation:e,onComplete:t}):C.extend({},C.fn.transition.settings,{animation:e})},animationClass:function(e){var t=e||u.animation,n=f.can.transition()&&!f.has.direction()?f.get.direction()+" ":"";return d.animating+" "+d.transition+" "+n+t},currentAnimation:function(){return!(!f.cache||f.cache.animation===S)&&f.cache.animation},currentDirection:function(){return f.is.inward()?d.inward:d.outward},direction:function(){return f.is.hidden()||!f.is.visible()?d.inward:d.outward},animationDirection:function(e){var n;return"string"==typeof(e=e||u.animation)&&(e=e.split(" "),C.each(e,function(e,t){t===d.inward?n=d.inward:t===d.outward&&(n=d.outward)})),n||!1},duration:function(e){return!1===(e=e||u.duration)&&(e=m.css("animation-duration")||0),"string"==typeof e?-1<e.indexOf("ms")?parseFloat(e):1e3*parseFloat(e):e},displayType:function(e){return e=e===S||e,u.displayType?u.displayType:(e&&m.data(n.displayType)===S&&f.can.transition(!0),m.data(n.displayType))},userStyle:function(e){return(e=e||m.attr("style")||"").replace(/display.*?;/,"")},transitionExists:function(e){return C.fn.transition.exists[e]},animationStartEvent:function(){var e,t=w.createElement("div"),n={animation:"animationstart",OAnimation:"oAnimationStart",MozAnimation:"mozAnimationStart",WebkitAnimation:"webkitAnimationStart"};for(e in n)if(t.style[e]!==S)return n[e];return!1},animationEndEvent:function(){var e,t=w.createElement("div"),n={animation:"animationend",OAnimation:"oAnimationEnd",MozAnimation:"mozAnimationEnd",WebkitAnimation:"webkitAnimationEnd"};for(e in n)if(t.style[e]!==S)return n[e];return!1}},can:{transition:function(e){var t,n,i,o,a,r,s=u.animation,l=f.get.transitionExists(s),c=f.get.displayType(!1);if(l===S||e){if(f.verbose("Determining whether animation exists"),t=m.attr("class"),n=m.prop("tagName"),o=(i=C("<"+n+" />").addClass(t).insertAfter(m)).addClass(s).removeClass(d.inward).removeClass(d.outward).addClass(d.animating).addClass(d.transition).css("animationName"),a=i.addClass(d.inward).css("animationName"),c||(c=i.attr("class",t).removeAttr("style").removeClass(d.hidden).removeClass(d.visible).show().css("display"),f.verbose("Determining final display state",c),f.save.displayType(c)),i.remove(),o!=a)f.debug("Direction exists for animation",s),r=!0;else{if("none"==o||!o)return void f.debug("No animation defined in css",s);f.debug("Static animation found",s,c),r=!1}f.save.transitionExists(s,r)}return l!==S?l:r},animate:function(){return f.can.transition()!==S}},is:{animating:function(){return m.hasClass(d.animating)},inward:function(){return m.hasClass(d.inward)},outward:function(){return m.hasClass(d.outward)},looping:function(){return m.hasClass(d.looping)},occurring:function(e){return e="."+(e=e||u.animation).replace(" ","."),0<m.filter(e).length},visible:function(){return m.is(":visible")},hidden:function(){return"hidden"===m.css("visibility")},supported:function(){return!1!==o}},hide:function(){f.verbose("Hiding element"),f.is.animating()&&f.reset(),l.blur(),f.remove.display(),f.remove.visible(),f.set.hidden(),f.force.hidden(),u.onHide.call(l),u.onComplete.call(l)},show:function(e){f.verbose("Showing element",e),f.remove.hidden(),f.set.visible(),f.force.visible(),u.onShow.call(l),u.onComplete.call(l)},toggle:function(){f.is.visible()?f.hide():f.show()},stop:function(){f.debug("Stopping current animation"),m.triggerHandler(o)},stopAll:function(){f.debug("Stopping all animation"),f.remove.queueCallback(),m.triggerHandler(o)},clear:{queue:function(){f.debug("Clearing animation queue"),f.remove.queueCallback()}},enable:function(){f.verbose("Starting animation"),m.removeClass(d.disabled)},disable:function(){f.debug("Stopping animation"),m.addClass(d.disabled)},setting:function(e,t){if(f.debug("Changing setting",e,t),C.isPlainObject(e))C.extend(!0,u,e);else{if(t===S)return u[e];C.isPlainObject(u[e])?C.extend(!0,u[e],t):u[e]=t}},internal:function(e,t){if(C.isPlainObject(e))C.extend(!0,f,e);else{if(t===S)return f[e];f[e]=t}},debug:function(){!u.silent&&u.debug&&(u.performance?f.performance.log(arguments):(f.debug=Function.prototype.bind.call(console.info,console,u.name+":"),f.debug.apply(console,arguments)))},verbose:function(){!u.silent&&u.verbose&&u.debug&&(u.performance?f.performance.log(arguments):(f.verbose=Function.prototype.bind.call(console.info,console,u.name+":"),f.verbose.apply(console,arguments)))},error:function(){u.silent||(f.error=Function.prototype.bind.call(console.error,console,u.name+":"),f.error.apply(console,arguments))},performance:{log:function(e){var t,n;u.performance&&(n=(t=(new Date).getTime())-(p||t),p=t,h.push({Name:e[0],Arguments:[].slice.call(e,1)||"",Element:l,"Execution Time":n})),clearTimeout(f.performance.timer),f.performance.timer=setTimeout(f.performance.display,500)},display:function(){var e=u.name+":",n=0;p=!1,clearTimeout(f.performance.timer),C.each(h,function(e,t){n+=t["Execution Time"]}),e+=" "+n+"ms",g&&(e+=" '"+g+"'"),1<r.length&&(e+=" ("+r.length+")"),(console.group!==S||console.table!==S)&&0<h.length&&(console.groupCollapsed(e),console.table?console.table(h):C.each(h,function(e,t){console.log(t.Name+": "+t["Execution Time"]+"ms")}),console.groupEnd()),h=[]}},invoke:function(i,e,t){var o,a,n,r=s;return e=e||y,t=l||t,"string"==typeof i&&r!==S&&(i=i.split(/[\. ]/),o=i.length-1,C.each(i,function(e,t){var n=e!=o?t+i[e+1].charAt(0).toUpperCase()+i[e+1].slice(1):i;if(C.isPlainObject(r[n])&&e!=o)r=r[n];else{if(r[n]!==S)return a=r[n],!1;if(!C.isPlainObject(r[t])||e==o)return r[t]!==S&&(a=r[t]),!1;r=r[t]}})),C.isFunction(a)?n=a.apply(t,e):a!==S&&(n=a),C.isArray(c)?c.push(n):c!==S?c=[c,n]:n!==S&&(c=n),a!==S&&a}}).initialize()}),c!==S?c:this},C.fn.transition.exists={},C.fn.transition.settings={name:"Transition",silent:!1,debug:!1,verbose:!1,performance:!0,namespace:"transition",interval:0,reverse:"auto",onStart:function(){},onComplete:function(){},onShow:function(){},onHide:function(){},useFailSafe:!0,failSafeDelay:100,allowRepeats:!1,displayType:!1,animation:"fade",duration:!1,queue:!0,metadata:{displayType:"display"},className:{animating:"animating",disabled:"disabled",hidden:"hidden",inward:"in",loading:"loading",looping:"looping",outward:"out",transition:"transition",visible:"visible"},error:{noAnimation:"Element is no longer attached to DOM. Unable to animate.  Use silent setting to surpress this warning in production.",repeated:"That animation is already occurring, cancelling repeated animation",method:"The method you called is not defined",support:"This browser does not support CSS animations"}}}(jQuery,window,document),function(P,E,e,F){"use strict";E=void 0!==E&&E.Math==Math?E:"undefined"!=typeof self&&self.Math==Math?self:Function("return this")();P.api=P.fn.api=function(x){var C,e=P.isFunction(this)?P(E):P(this),w=e.selector||"",S=(new Date).getTime(),k=[],T=x,A="string"==typeof T,R=[].slice.call(arguments,1);return e.each(function(){var a,r,n,e,s,l,c=P.isPlainObject(x)?P.extend(!0,{},P.fn.api.settings,x):P.extend({},P.fn.api.settings),t=c.namespace,i=c.metadata,o=c.selector,u=c.error,d=c.className,f="."+t,m="module-"+t,g=P(this),p=g.closest(o.form),h=c.stateContext?P(c.stateContext):g,v=this,b=h[0],y=g.data(m);l={initialize:function(){A||l.bind.events(),l.instantiate()},instantiate:function(){l.verbose("Storing instance of module",l),y=l,g.data(m,y)},destroy:function(){l.verbose("Destroying previous module for",v),g.removeData(m).off(f)},bind:{events:function(){var e=l.get.event();e?(l.verbose("Attaching API events to element",e),g.on(e+f,l.event.trigger)):"now"==c.on&&(l.debug("Querying API endpoint immediately"),l.query())}},decode:{json:function(e){if(e!==F&&"string"==typeof e)try{e=JSON.parse(e)}catch(e){}return e}},read:{cachedResponse:function(e){var t;if(E.Storage!==F)return t=sessionStorage.getItem(e),l.debug("Using cached response",e,t),t=l.decode.json(t);l.error(u.noStorage)}},write:{cachedResponse:function(e,t){t&&""===t?l.debug("Response empty, not caching",t):E.Storage!==F?(P.isPlainObject(t)&&(t=JSON.stringify(t)),sessionStorage.setItem(e,t),l.verbose("Storing cached response for url",e,t)):l.error(u.noStorage)}},query:function(){if(l.is.disabled())l.debug("Element is disabled API request aborted");else{if(l.is.loading()){if(!c.interruptRequests)return void l.debug("Cancelling request, previous request is still pending");l.debug("Interrupting previous request"),l.abort()}if(c.defaultData&&P.extend(!0,c.urlData,l.get.defaultData()),c.serializeForm&&(c.data=l.add.formData(c.data)),!1===(r=l.get.settings()))return l.cancelled=!0,void l.error(u.beforeSend);if(l.cancelled=!1,(n=l.get.templatedURL())||l.is.mocked()){if((n=l.add.urlData(n))||l.is.mocked()){if(r.url=c.base+n,a=P.extend(!0,{},c,{type:c.method||c.type,data:e,url:c.base+n,beforeSend:c.beforeXHR,success:function(){},failure:function(){},complete:function(){}}),l.debug("Querying URL",a.url),l.verbose("Using AJAX settings",a),"local"===c.cache&&l.read.cachedResponse(n))return l.debug("Response returned from local cache"),l.request=l.create.request(),void l.request.resolveWith(b,[l.read.cachedResponse(n)]);c.throttle?c.throttleFirstRequest||l.timer?(l.debug("Throttling request",c.throttle),clearTimeout(l.timer),l.timer=setTimeout(function(){l.timer&&delete l.timer,l.debug("Sending throttled request",e,a.method),l.send.request()},c.throttle)):(l.debug("Sending request",e,a.method),l.send.request(),l.timer=setTimeout(function(){},c.throttle)):(l.debug("Sending request",e,a.method),l.send.request())}}else l.error(u.missingURL)}},should:{removeError:function(){return!0===c.hideError||"auto"===c.hideError&&!l.is.form()}},is:{disabled:function(){return 0<g.filter(o.disabled).length},expectingJSON:function(){return"json"===c.dataType||"jsonp"===c.dataType},form:function(){return g.is("form")||h.is("form")},mocked:function(){return c.mockResponse||c.mockResponseAsync||c.response||c.responseAsync},input:function(){return g.is("input")},loading:function(){return!!l.request&&"pending"==l.request.state()},abortedRequest:function(e){return e&&e.readyState!==F&&0===e.readyState?(l.verbose("XHR request determined to be aborted"),!0):(l.verbose("XHR request was not aborted"),!1)},validResponse:function(e){return l.is.expectingJSON()&&P.isFunction(c.successTest)?(l.debug("Checking JSON returned success",c.successTest,e),c.successTest(e)?(l.debug("Response passed success test",e),!0):(l.debug("Response failed success test",e),!1)):(l.verbose("Response is not JSON, skipping validation",c.successTest,e),!0)}},was:{cancelled:function(){return l.cancelled||!1},succesful:function(){return l.request&&"resolved"==l.request.state()},failure:function(){return l.request&&"rejected"==l.request.state()},complete:function(){return l.request&&("resolved"==l.request.state()||"rejected"==l.request.state())}},add:{urlData:function(o,a){var e,t;return o&&(e=o.match(c.regExp.required),t=o.match(c.regExp.optional),a=a||c.urlData,e&&(l.debug("Looking for required URL variables",e),P.each(e,function(e,t){var n=-1!==t.indexOf("$")?t.substr(2,t.length-3):t.substr(1,t.length-2),i=P.isPlainObject(a)&&a[n]!==F?a[n]:g.data(n)!==F?g.data(n):h.data(n)!==F?h.data(n):a[n];if(i===F)return l.error(u.requiredParameter,n,o),o=!1;l.verbose("Found required variable",n,i),i=c.encodeParameters?l.get.urlEncodedValue(i):i,o=o.replace(t,i)})),t&&(l.debug("Looking for optional URL variables",e),P.each(t,function(e,t){var n=-1!==t.indexOf("$")?t.substr(3,t.length-4):t.substr(2,t.length-3),i=P.isPlainObject(a)&&a[n]!==F?a[n]:g.data(n)!==F?g.data(n):h.data(n)!==F?h.data(n):a[n];o=i!==F?(l.verbose("Optional variable Found",n,i),o.replace(t,i)):(l.verbose("Optional variable not found",n),-1!==o.indexOf("/"+t)?o.replace("/"+t,""):o.replace(t,""))}))),o},formData:function(e){var t=P.fn.serializeObject!==F,n=t?p.serializeObject():p.serialize();return e=e||c.data,e=P.isPlainObject(e)?t?(l.debug("Extending existing data with form data",e,n),P.extend(!0,{},e,n)):(l.error(u.missingSerialize),l.debug("Cant extend data. Replacing data with form data",e,n),n):(l.debug("Adding form data",n),n)}},send:{request:function(){l.set.loading(),l.request=l.create.request(),l.is.mocked()?l.mockedXHR=l.create.mockedXHR():l.xhr=l.create.xhr(),c.onRequest.call(b,l.request,l.xhr)}},event:{trigger:function(e){l.query(),"submit"!=e.type&&"click"!=e.type||e.preventDefault()},xhr:{always:function(){},done:function(e,t,n){var i=this,o=(new Date).getTime()-s,a=c.loadingDuration-o,r=!!P.isFunction(c.onResponse)&&(l.is.expectingJSON()?c.onResponse.call(i,P.extend(!0,{},e)):c.onResponse.call(i,e));a=0<a?a:0,r&&(l.debug("Modified API response in onResponse callback",c.onResponse,r,e),e=r),0<a&&l.debug("Response completed early delaying state change by",a),setTimeout(function(){l.is.validResponse(e)?l.request.resolveWith(i,[e,n]):l.request.rejectWith(i,[n,"invalid"])},a)},fail:function(e,t,n){var i=this,o=(new Date).getTime()-s,a=c.loadingDuration-o;0<(a=0<a?a:0)&&l.debug("Response completed early delaying state change by",a),setTimeout(function(){l.is.abortedRequest(e)?l.request.rejectWith(i,[e,"aborted",n]):l.request.rejectWith(i,[e,"error",t,n])},a)}},request:{done:function(e,t){l.debug("Successful API Response",e),"local"===c.cache&&n&&(l.write.cachedResponse(n,e),l.debug("Saving server response locally",l.cache)),c.onSuccess.call(b,e,g,t)},complete:function(e,t){var n,i;l.was.succesful()?(i=e,n=t):(n=e,i=l.get.responseFromXHR(n)),l.remove.loading(),c.onComplete.call(b,i,g,n)},fail:function(e,t,n){var i=l.get.responseFromXHR(e),o=l.get.errorFromRequest(i,t,n);if("aborted"==t)return l.debug("XHR Aborted (Most likely caused by page navigation or CORS Policy)",t,n),c.onAbort.call(b,t,g,e),!0;"invalid"==t?l.debug("JSON did not pass success test. A server-side error has most likely occurred",i):"error"==t&&e!==F&&(l.debug("XHR produced a server error",t,n),200!=e.status&&n!==F&&""!==n&&l.error(u.statusMessage+n,a.url),c.onError.call(b,o,g,e)),c.errorDuration&&"aborted"!==t&&(l.debug("Adding error state"),l.set.error(),l.should.removeError()&&setTimeout(l.remove.error,c.errorDuration)),l.debug("API Request failed",o,e),c.onFailure.call(b,i,g,e)}}},create:{request:function(){return P.Deferred().always(l.event.request.complete).done(l.event.request.done).fail(l.event.request.fail)},mockedXHR:function(){var e,t,n,i=c.mockResponse||c.response,o=c.mockResponseAsync||c.responseAsync;return n=P.Deferred().always(l.event.xhr.complete).done(l.event.xhr.done).fail(l.event.xhr.fail),i?(t=P.isFunction(i)?(l.debug("Using specified synchronous callback",i),i.call(b,r)):(l.debug("Using settings specified response",i),i),n.resolveWith(b,[t,!1,{responseText:t}])):P.isFunction(o)&&(e=function(e){l.debug("Async callback returned response",e),e?n.resolveWith(b,[e,!1,{responseText:e}]):n.rejectWith(b,[{responseText:e},!1,!1])},l.debug("Using specified async response callback",o),o.call(b,r,e)),n},xhr:function(){var e;return e=P.ajax(a).always(l.event.xhr.always).done(l.event.xhr.done).fail(l.event.xhr.fail),l.verbose("Created server request",e,a),e}},set:{error:function(){l.verbose("Adding error state to element",h),h.addClass(d.error)},loading:function(){l.verbose("Adding loading state to element",h),h.addClass(d.loading),s=(new Date).getTime()}},remove:{error:function(){l.verbose("Removing error state from element",h),h.removeClass(d.error)},loading:function(){l.verbose("Removing loading state from element",h),h.removeClass(d.loading)}},get:{responseFromXHR:function(e){return!!P.isPlainObject(e)&&(l.is.expectingJSON()?l.decode.json(e.responseText):e.responseText)},errorFromRequest:function(e,t,n){return P.isPlainObject(e)&&e.error!==F?e.error:c.error[t]!==F?c.error[t]:n},request:function(){return l.request||!1},xhr:function(){return l.xhr||!1},settings:function(){var e;return(e=c.beforeSend.call(b,c))&&(e.success!==F&&(l.debug("Legacy success callback detected",e),l.error(u.legacyParameters,e.success),e.onSuccess=e.success),e.failure!==F&&(l.debug("Legacy failure callback detected",e),l.error(u.legacyParameters,e.failure),e.onFailure=e.failure),e.complete!==F&&(l.debug("Legacy complete callback detected",e),l.error(u.legacyParameters,e.complete),e.onComplete=e.complete)),e===F&&l.error(u.noReturnedValue),!1===e?e:e!==F?P.extend(!0,{},e):P.extend(!0,{},c)},urlEncodedValue:function(e){var t=E.decodeURIComponent(e),n=E.encodeURIComponent(e);return t!==e?(l.debug("URL value is already encoded, avoiding double encoding",e),e):(l.verbose("Encoding value using encodeURIComponent",e,n),n)},defaultData:function(){var e={};return P.isWindow(v)||(l.is.input()?e.value=g.val():l.is.form()||(e.text=g.text())),e},event:function(){return P.isWindow(v)||"now"==c.on?(l.debug("API called without element, no events attached"),!1):"auto"==c.on?g.is("input")?v.oninput!==F?"input":v.onpropertychange!==F?"propertychange":"keyup":g.is("form")?"submit":"click":c.on},templatedURL:function(e){if(e=e||g.data(i.action)||c.action||!1,n=g.data(i.url)||c.url||!1)return l.debug("Using specified url",n),n;if(e){if(l.debug("Looking up url for action",e,c.api),c.api[e]===F&&!l.is.mocked())return void l.error(u.missingAction,c.action,c.api);n=c.api[e]}else l.is.form()&&(n=g.attr("action")||h.attr("action")||!1,l.debug("No url or action specified, defaulting to form action",n));return n}},abort:function(){var e=l.get.xhr();e&&"resolved"!==e.state()&&(l.debug("Cancelling API request"),e.abort())},reset:function(){l.remove.error(),l.remove.loading()},setting:function(e,t){if(l.debug("Changing setting",e,t),P.isPlainObject(e))P.extend(!0,c,e);else{if(t===F)return c[e];P.isPlainObject(c[e])?P.extend(!0,c[e],t):c[e]=t}},internal:function(e,t){if(P.isPlainObject(e))P.extend(!0,l,e);else{if(t===F)return l[e];l[e]=t}},debug:function(){!c.silent&&c.debug&&(c.performance?l.performance.log(arguments):(l.debug=Function.prototype.bind.call(console.info,console,c.name+":"),l.debug.apply(console,arguments)))},verbose:function(){!c.silent&&c.verbose&&c.debug&&(c.performance?l.performance.log(arguments):(l.verbose=Function.prototype.bind.call(console.info,console,c.name+":"),l.verbose.apply(console,arguments)))},error:function(){c.silent||(l.error=Function.prototype.bind.call(console.error,console,c.name+":"),l.error.apply(console,arguments))},performance:{log:function(e){var t,n;c.performance&&(n=(t=(new Date).getTime())-(S||t),S=t,k.push({Name:e[0],Arguments:[].slice.call(e,1)||"","Execution Time":n})),clearTimeout(l.performance.timer),l.performance.timer=setTimeout(l.performance.display,500)},display:function(){var e=c.name+":",n=0;S=!1,clearTimeout(l.performance.timer),P.each(k,function(e,t){n+=t["Execution Time"]}),e+=" "+n+"ms",w&&(e+=" '"+w+"'"),(console.group!==F||console.table!==F)&&0<k.length&&(console.groupCollapsed(e),console.table?console.table(k):P.each(k,function(e,t){console.log(t.Name+": "+t["Execution Time"]+"ms")}),console.groupEnd()),k=[]}},invoke:function(i,e,t){var o,a,n,r=y;return e=e||R,t=v||t,"string"==typeof i&&r!==F&&(i=i.split(/[\. ]/),o=i.length-1,P.each(i,function(e,t){var n=e!=o?t+i[e+1].charAt(0).toUpperCase()+i[e+1].slice(1):i;if(P.isPlainObject(r[n])&&e!=o)r=r[n];else{if(r[n]!==F)return a=r[n],!1;if(!P.isPlainObject(r[t])||e==o)return r[t]!==F?a=r[t]:l.error(u.method,i),!1;r=r[t]}})),P.isFunction(a)?n=a.apply(t,e):a!==F&&(n=a),P.isArray(C)?C.push(n):C!==F?C=[C,n]:n!==F&&(C=n),a}},A?(y===F&&l.initialize(),l.invoke(T)):(y!==F&&y.invoke("destroy"),l.initialize())}),C!==F?C:this},P.api.settings={name:"API",namespace:"api",debug:!1,verbose:!1,performance:!0,api:{},cache:!0,interruptRequests:!0,on:"auto",stateContext:!1,loadingDuration:0,hideError:"auto",errorDuration:2e3,encodeParameters:!0,action:!1,url:!1,base:"",urlData:{},defaultData:!0,serializeForm:!1,throttle:0,throttleFirstRequest:!0,method:"get",data:{},dataType:"json",mockResponse:!1,mockResponseAsync:!1,response:!1,responseAsync:!1,beforeSend:function(e){return e},beforeXHR:function(e){},onRequest:function(e,t){},onResponse:!1,onSuccess:function(e,t){},onComplete:function(e,t){},onFailure:function(e,t){},onError:function(e,t){},onAbort:function(e,t){},successTest:!1,error:{beforeSend:"The before send function has aborted the request",error:"There was an error with your request",exitConditions:"API Request Aborted. Exit conditions met",JSONParse:"JSON could not be parsed during error handling",legacyParameters:"You are using legacy API success callback names",method:"The method you called is not defined",missingAction:"API action used but no url was defined",missingSerialize:"jquery-serialize-object is required to add form data to an existing data object",missingURL:"No URL specified for api event",noReturnedValue:"The beforeSend callback must return a settings object, beforeSend ignored.",noStorage:"Caching responses locally requires session storage",parseError:"There was an error parsing your request",requiredParameter:"Missing a required URL parameter: ",statusMessage:"Server gave an error: ",timeout:"Your request timed out"},regExp:{required:/\{\$*[A-z0-9]+\}/g,optional:/\{\/\$*[A-z0-9]+\}/g},className:{loading:"loading",error:"error"},selector:{disabled:".disabled",form:"form"},metadata:{action:"action",url:"url"}}}(jQuery,window,document),function(P,E,F,O){"use strict";E=void 0!==E&&E.Math==Math?E:"undefined"!=typeof self&&self.Math==Math?self:Function("return this")(),P.fn.visibility=function(b){var y,e=P(this),x=e.selector||"",C=(new Date).getTime(),w=[],S=b,k="string"==typeof S,T=[].slice.call(arguments,1),A=e.length,R=0;return e.each(function(){var e,t,n,s,o=P.isPlainObject(b)?P.extend(!0,{},P.fn.visibility.settings,b):P.extend({},P.fn.visibility.settings),i=o.className,a=o.namespace,l=o.error,r=o.metadata,c="."+a,u="module-"+a,d=P(E),f=P(this),m=P(o.context),g=(f.selector,f.data(u)),p=E.requestAnimationFrame||E.mozRequestAnimationFrame||E.webkitRequestAnimationFrame||E.msRequestAnimationFrame||function(e){setTimeout(e,0)},h=this,v=!1;s={initialize:function(){s.debug("Initializing",o),s.setup.cache(),s.should.trackChanges()&&("image"==o.type&&s.setup.image(),"fixed"==o.type&&s.setup.fixed(),o.observeChanges&&s.observeChanges(),s.bind.events()),s.save.position(),s.is.visible()||s.error(l.visible,f),o.initialCheck&&s.checkVisibility(),s.instantiate()},instantiate:function(){s.debug("Storing instance",s),f.data(u,s),g=s},destroy:function(){s.verbose("Destroying previous module"),n&&n.disconnect(),t&&t.disconnect(),d.off("load"+c,s.event.load).off("resize"+c,s.event.resize),m.off("scroll"+c,s.event.scroll).off("scrollchange"+c,s.event.scrollchange),"fixed"==o.type&&(s.resetFixed(),s.remove.placeholder()),f.off(c).removeData(u)},observeChanges:function(){"MutationObserver"in E&&(t=new MutationObserver(s.event.contextChanged),n=new MutationObserver(s.event.changed),t.observe(F,{childList:!0,subtree:!0}),n.observe(h,{childList:!0,subtree:!0}),s.debug("Setting up mutation observer",n))},bind:{events:function(){s.verbose("Binding visibility events to scroll and resize"),o.refreshOnLoad&&d.on("load"+c,s.event.load),d.on("resize"+c,s.event.resize),m.off("scroll"+c).on("scroll"+c,s.event.scroll).on("scrollchange"+c,s.event.scrollchange)}},event:{changed:function(e){s.verbose("DOM tree modified, updating visibility calculations"),s.timer=setTimeout(function(){s.verbose("DOM tree modified, updating sticky menu"),s.refresh()},100)},contextChanged:function(e){[].forEach.call(e,function(e){e.removedNodes&&[].forEach.call(e.removedNodes,function(e){(e==h||0<P(e).find(h).length)&&(s.debug("Element removed from DOM, tearing down events"),s.destroy())})})},resize:function(){s.debug("Window resized"),o.refreshOnResize&&p(s.refresh)},load:function(){s.debug("Page finished loading"),p(s.refresh)},scroll:function(){o.throttle?(clearTimeout(s.timer),s.timer=setTimeout(function(){m.triggerHandler("scrollchange"+c,[m.scrollTop()])},o.throttle)):p(function(){m.triggerHandler("scrollchange"+c,[m.scrollTop()])})},scrollchange:function(e,t){s.checkVisibility(t)}},precache:function(e,t){e instanceof Array||(e=[e]);for(var n=e.length,i=0,o=[],a=F.createElement("img"),r=function(){++i>=e.length&&P.isFunction(t)&&t()};n--;)(a=F.createElement("img")).onload=r,a.onerror=r,a.src=e[n],o.push(a)},enableCallbacks:function(){s.debug("Allowing callbacks to occur"),v=!1},disableCallbacks:function(){s.debug("Disabling all callbacks temporarily"),v=!0},should:{trackChanges:function(){return k?(s.debug("One time query, no need to bind events"),!1):(s.debug("Callbacks being attached"),!0)}},setup:{cache:function(){s.cache={occurred:{},screen:{},element:{}}},image:function(){var e=f.data(r.src);e&&(s.verbose("Lazy loading image",e),o.once=!0,o.observeChanges=!1,o.onOnScreen=function(){s.debug("Image on screen",h),s.precache(e,function(){s.set.image(e,function(){++R==A&&o.onAllLoaded.call(this),o.onLoad.call(this)})})})},fixed:function(){s.debug("Setting up fixed"),o.once=!1,o.observeChanges=!1,o.initialCheck=!0,o.refreshOnLoad=!0,b.transition||(o.transition=!1),s.create.placeholder(),s.debug("Added placeholder",e),o.onTopPassed=function(){s.debug("Element passed, adding fixed position",f),s.show.placeholder(),s.set.fixed(),o.transition&&P.fn.transition!==O&&f.transition(o.transition,o.duration)},o.onTopPassedReverse=function(){s.debug("Element returned to position, removing fixed",f),s.hide.placeholder(),s.remove.fixed()}}},create:{placeholder:function(){s.verbose("Creating fixed position placeholder"),e=f.clone(!1).css("display","none").addClass(i.placeholder).insertAfter(f)}},show:{placeholder:function(){s.verbose("Showing placeholder"),e.css("display","block").css("visibility","hidden")}},hide:{placeholder:function(){s.verbose("Hiding placeholder"),e.css("display","none").css("visibility","")}},set:{fixed:function(){s.verbose("Setting element to fixed position"),f.addClass(i.fixed).css({position:"fixed",top:o.offset+"px",left:"auto",zIndex:o.zIndex}),o.onFixed.call(h)},image:function(e,t){if(f.attr("src",e),o.transition)if(P.fn.transition!==O){if(f.hasClass(i.visible))return void s.debug("Transition already occurred on this image, skipping animation");f.transition(o.transition,o.duration,t)}else f.fadeIn(o.duration,t);else f.show()}},is:{onScreen:function(){return s.get.elementCalculations().onScreen},offScreen:function(){return s.get.elementCalculations().offScreen},visible:function(){return!(!s.cache||!s.cache.element)&&!(0===s.cache.element.width&&0===s.cache.element.offset.top)},verticallyScrollableContext:function(){var e=m.get(0)!==E&&m.css("overflow-y");return"auto"==e||"scroll"==e},horizontallyScrollableContext:function(){var e=m.get(0)!==E&&m.css("overflow-x");return"auto"==e||"scroll"==e}},refresh:function(){s.debug("Refreshing constants (width/height)"),"fixed"==o.type&&s.resetFixed(),s.reset(),s.save.position(),o.checkOnRefresh&&s.checkVisibility(),o.onRefresh.call(h)},resetFixed:function(){s.remove.fixed(),s.remove.occurred()},reset:function(){s.verbose("Resetting all cached values"),P.isPlainObject(s.cache)&&(s.cache.screen={},s.cache.element={})},checkVisibility:function(e){s.verbose("Checking visibility of element",s.cache.element),!v&&s.is.visible()&&(s.save.scroll(e),s.save.calculations(),s.passed(),s.passingReverse(),s.topVisibleReverse(),s.bottomVisibleReverse(),s.topPassedReverse(),s.bottomPassedReverse(),s.onScreen(),s.offScreen(),s.passing(),s.topVisible(),s.bottomVisible(),s.topPassed(),s.bottomPassed(),o.onUpdate&&o.onUpdate.call(h,s.get.elementCalculations()))},passed:function(e,t){var n=s.get.elementCalculations();if(e&&t)o.onPassed[e]=t;else{if(e!==O)return s.get.pixelsPassed(e)>n.pixelsPassed;n.passing&&P.each(o.onPassed,function(e,t){n.bottomVisible||n.pixelsPassed>s.get.pixelsPassed(e)?s.execute(t,e):o.once||s.remove.occurred(t)})}},onScreen:function(e){var t=s.get.elementCalculations(),n=e||o.onOnScreen,i="onScreen";if(e&&(s.debug("Adding callback for onScreen",e),o.onOnScreen=e),t.onScreen?s.execute(n,i):o.once||s.remove.occurred(i),e!==O)return t.onOnScreen},offScreen:function(e){var t=s.get.elementCalculations(),n=e||o.onOffScreen,i="offScreen";if(e&&(s.debug("Adding callback for offScreen",e),o.onOffScreen=e),t.offScreen?s.execute(n,i):o.once||s.remove.occurred(i),e!==O)return t.onOffScreen},passing:function(e){var t=s.get.elementCalculations(),n=e||o.onPassing,i="passing";if(e&&(s.debug("Adding callback for passing",e),o.onPassing=e),t.passing?s.execute(n,i):o.once||s.remove.occurred(i),e!==O)return t.passing},topVisible:function(e){var t=s.get.elementCalculations(),n=e||o.onTopVisible,i="topVisible";if(e&&(s.debug("Adding callback for top visible",e),o.onTopVisible=e),t.topVisible?s.execute(n,i):o.once||s.remove.occurred(i),e===O)return t.topVisible},bottomVisible:function(e){var t=s.get.elementCalculations(),n=e||o.onBottomVisible,i="bottomVisible";if(e&&(s.debug("Adding callback for bottom visible",e),o.onBottomVisible=e),t.bottomVisible?s.execute(n,i):o.once||s.remove.occurred(i),e===O)return t.bottomVisible},topPassed:function(e){var t=s.get.elementCalculations(),n=e||o.onTopPassed,i="topPassed";if(e&&(s.debug("Adding callback for top passed",e),o.onTopPassed=e),t.topPassed?s.execute(n,i):o.once||s.remove.occurred(i),e===O)return t.topPassed},bottomPassed:function(e){var t=s.get.elementCalculations(),n=e||o.onBottomPassed,i="bottomPassed";if(e&&(s.debug("Adding callback for bottom passed",e),o.onBottomPassed=e),t.bottomPassed?s.execute(n,i):o.once||s.remove.occurred(i),e===O)return t.bottomPassed},passingReverse:function(e){var t=s.get.elementCalculations(),n=e||o.onPassingReverse,i="passingReverse";if(e&&(s.debug("Adding callback for passing reverse",e),o.onPassingReverse=e),t.passing?o.once||s.remove.occurred(i):s.get.occurred("passing")&&s.execute(n,i),e!==O)return!t.passing},topVisibleReverse:function(e){var t=s.get.elementCalculations(),n=e||o.onTopVisibleReverse,i="topVisibleReverse";if(e&&(s.debug("Adding callback for top visible reverse",e),o.onTopVisibleReverse=e),t.topVisible?o.once||s.remove.occurred(i):s.get.occurred("topVisible")&&s.execute(n,i),e===O)return!t.topVisible},bottomVisibleReverse:function(e){var t=s.get.elementCalculations(),n=e||o.onBottomVisibleReverse,i="bottomVisibleReverse";if(e&&(s.debug("Adding callback for bottom visible reverse",e),o.onBottomVisibleReverse=e),t.bottomVisible?o.once||s.remove.occurred(i):s.get.occurred("bottomVisible")&&s.execute(n,i),e===O)return!t.bottomVisible},topPassedReverse:function(e){var t=s.get.elementCalculations(),n=e||o.onTopPassedReverse,i="topPassedReverse";if(e&&(s.debug("Adding callback for top passed reverse",e),o.onTopPassedReverse=e),t.topPassed?o.once||s.remove.occurred(i):s.get.occurred("topPassed")&&s.execute(n,i),e===O)return!t.onTopPassed},bottomPassedReverse:function(e){var t=s.get.elementCalculations(),n=e||o.onBottomPassedReverse,i="bottomPassedReverse";if(e&&(s.debug("Adding callback for bottom passed reverse",e),o.onBottomPassedReverse=e),t.bottomPassed?o.once||s.remove.occurred(i):s.get.occurred("bottomPassed")&&s.execute(n,i),e===O)return!t.bottomPassed},execute:function(e,t){var n=s.get.elementCalculations(),i=s.get.screenCalculations();(e=e||!1)&&(o.continuous?(s.debug("Callback being called continuously",t,n),e.call(h,n,i)):s.get.occurred(t)||(s.debug("Conditions met",t,n),e.call(h,n,i))),s.save.occurred(t)},remove:{fixed:function(){s.debug("Removing fixed position"),f.removeClass(i.fixed).css({position:"",top:"",left:"",zIndex:""}),o.onUnfixed.call(h)},placeholder:function(){s.debug("Removing placeholder content"),e&&e.remove()},occurred:function(e){if(e){var t=s.cache.occurred;t[e]!==O&&!0===t[e]&&(s.debug("Callback can now be called again",e),s.cache.occurred[e]=!1)}else s.cache.occurred={}}},save:{calculations:function(){s.verbose("Saving all calculations necessary to determine positioning"),s.save.direction(),s.save.screenCalculations(),s.save.elementCalculations()},occurred:function(e){e&&(s.cache.occurred[e]!==O&&!0===s.cache.occurred[e]||(s.verbose("Saving callback occurred",e),s.cache.occurred[e]=!0))},scroll:function(e){e=e+o.offset||m.scrollTop()+o.offset,s.cache.scroll=e},direction:function(){var e,t=s.get.scroll(),n=s.get.lastScroll();return e=n<t&&n?"down":t<n&&n?"up":"static",s.cache.direction=e,s.cache.direction},elementPosition:function(){var e=s.cache.element,t=s.get.screenSize();return s.verbose("Saving element position"),e.fits=e.height<t.height,e.offset=f.offset(),e.width=f.outerWidth(),e.height=f.outerHeight(),s.is.verticallyScrollableContext()&&(e.offset.top+=m.scrollTop()-m.offset().top),s.is.horizontallyScrollableContext()&&(e.offset.left+=m.scrollLeft-m.offset().left),s.cache.element=e},elementCalculations:function(){var e=s.get.screenCalculations(),t=s.get.elementPosition();return o.includeMargin?(t.margin={},t.margin.top=parseInt(f.css("margin-top"),10),t.margin.bottom=parseInt(f.css("margin-bottom"),10),t.top=t.offset.top-t.margin.top,t.bottom=t.offset.top+t.height+t.margin.bottom):(t.top=t.offset.top,t.bottom=t.offset.top+t.height),t.topPassed=e.top>=t.top,t.bottomPassed=e.top>=t.bottom,t.topVisible=e.bottom>=t.top&&!t.topPassed,t.bottomVisible=e.bottom>=t.bottom&&!t.bottomPassed,t.pixelsPassed=0,t.percentagePassed=0,t.onScreen=(t.topVisible||t.passing)&&!t.bottomPassed,t.passing=t.topPassed&&!t.bottomPassed,t.offScreen=!t.onScreen,t.passing&&(t.pixelsPassed=e.top-t.top,t.percentagePassed=(e.top-t.top)/t.height),s.cache.element=t,s.verbose("Updated element calculations",t),t},screenCalculations:function(){var e=s.get.scroll();return s.save.direction(),s.cache.screen.top=e,s.cache.screen.bottom=e+s.cache.screen.height,s.cache.screen},screenSize:function(){s.verbose("Saving window position"),s.cache.screen={height:m.height()}},position:function(){s.save.screenSize(),s.save.elementPosition()}},get:{pixelsPassed:function(e){var t=s.get.elementCalculations();return-1<e.search("%")?t.height*(parseInt(e,10)/100):parseInt(e,10)},occurred:function(e){return s.cache.occurred!==O&&s.cache.occurred[e]||!1},direction:function(){return s.cache.direction===O&&s.save.direction(),s.cache.direction},elementPosition:function(){return s.cache.element===O&&s.save.elementPosition(),s.cache.element},elementCalculations:function(){return s.cache.element===O&&s.save.elementCalculations(),s.cache.element},screenCalculations:function(){return s.cache.screen===O&&s.save.screenCalculations(),s.cache.screen},screenSize:function(){return s.cache.screen===O&&s.save.screenSize(),s.cache.screen},scroll:function(){return s.cache.scroll===O&&s.save.scroll(),s.cache.scroll},lastScroll:function(){return s.cache.screen===O?(s.debug("First scroll event, no last scroll could be found"),!1):s.cache.screen.top}},setting:function(e,t){if(P.isPlainObject(e))P.extend(!0,o,e);else{if(t===O)return o[e];o[e]=t}},internal:function(e,t){if(P.isPlainObject(e))P.extend(!0,s,e);else{if(t===O)return s[e];s[e]=t}},debug:function(){!o.silent&&o.debug&&(o.performance?s.performance.log(arguments):(s.debug=Function.prototype.bind.call(console.info,console,o.name+":"),s.debug.apply(console,arguments)))},verbose:function(){!o.silent&&o.verbose&&o.debug&&(o.performance?s.performance.log(arguments):(s.verbose=Function.prototype.bind.call(console.info,console,o.name+":"),s.verbose.apply(console,arguments)))},error:function(){o.silent||(s.error=Function.prototype.bind.call(console.error,console,o.name+":"),s.error.apply(console,arguments))},performance:{log:function(e){var t,n;o.performance&&(n=(t=(new Date).getTime())-(C||t),C=t,w.push({Name:e[0],Arguments:[].slice.call(e,1)||"",Element:h,"Execution Time":n})),clearTimeout(s.performance.timer),s.performance.timer=setTimeout(s.performance.display,500)},display:function(){var e=o.name+":",n=0;C=!1,clearTimeout(s.performance.timer),P.each(w,function(e,t){n+=t["Execution Time"]}),e+=" "+n+"ms",x&&(e+=" '"+x+"'"),(console.group!==O||console.table!==O)&&0<w.length&&(console.groupCollapsed(e),console.table?console.table(w):P.each(w,function(e,t){console.log(t.Name+": "+t["Execution Time"]+"ms")}),console.groupEnd()),w=[]}},invoke:function(i,e,t){var o,a,n,r=g;return e=e||T,t=h||t,"string"==typeof i&&r!==O&&(i=i.split(/[\. ]/),o=i.length-1,P.each(i,function(e,t){var n=e!=o?t+i[e+1].charAt(0).toUpperCase()+i[e+1].slice(1):i;if(P.isPlainObject(r[n])&&e!=o)r=r[n];else{if(r[n]!==O)return a=r[n],!1;if(!P.isPlainObject(r[t])||e==o)return r[t]!==O?a=r[t]:s.error(l.method,i),!1;r=r[t]}})),P.isFunction(a)?n=a.apply(t,e):a!==O&&(n=a),P.isArray(y)?y.push(n):y!==O?y=[y,n]:n!==O&&(y=n),a}},k?(g===O&&s.initialize(),g.save.scroll(),g.save.calculations(),s.invoke(S)):(g!==O&&g.invoke("destroy"),s.initialize())}),y!==O?y:this},P.fn.visibility.settings={name:"Visibility",namespace:"visibility",debug:!1,verbose:!1,performance:!0,observeChanges:!0,initialCheck:!0,refreshOnLoad:!0,refreshOnResize:!0,checkOnRefresh:!0,once:!0,continuous:!1,offset:0,includeMargin:!1,context:E,throttle:!1,type:!1,zIndex:"10",transition:"fade in",duration:1e3,onPassed:{},onOnScreen:!1,onOffScreen:!1,onPassing:!1,onTopVisible:!1,onBottomVisible:!1,onTopPassed:!1,onBottomPassed:!1,onPassingReverse:!1,onTopVisibleReverse:!1,onBottomVisibleReverse:!1,onTopPassedReverse:!1,onBottomPassedReverse:!1,onLoad:function(){},onAllLoaded:function(){},onFixed:function(){},onUnfixed:function(){},onUpdate:!1,onRefresh:function(){},metadata:{src:"src"},className:{fixed:"fixed",placeholder:"placeholder",visible:"visible"},error:{method:"The method you called is not defined.",visible:"Element is hidden, you must call refresh after element becomes visible"}}}(jQuery,window,document);
/* Copyright (C) 1991-2017 Free Software Foundation, Inc.
   This file is part of the GNU C Library.

   The GNU C Library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2.1 of the License, or (at your option) any later version.

   The GNU C Library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public
   License along with the GNU C Library; if not, see
   <http://www.gnu.org/licenses/>.  */
/* This header is separate from features.h so that the compiler can
   include it implicitly at the start of every compilation.  It must
   not itself include <features.h> or any other header that includes
   <features.h> because the implicit include comes before any feature
   test macros that may be defined in a source file before it first
   explicitly includes a system header.  GCC knows the name of this
   header in order to preinclude it.  */
/* glibc's intent is to support the IEC 559 math functionality, real
   and complex.  If the GCC (4.9 and later) predefined macros
   specifying compiler intent are available, use them to determine
   whether the overall intent is to support these features; otherwise,
   presume an older compiler has intent to support these features and
   define these macros by default.  */
/* wchar_t uses Unicode 8.0.0.  Version 8.0 of the Unicode Standard is
   synchronized with ISO/IEC 10646:2014, plus Amendment 1 (published
   2015-05-15).  */
/* We do not support C11 <threads.h>.  */
/*! jQuery v2.1.4 | (c) 2005, 2015 jQuery Foundation, Inc. | jquery.org/license */
!function(a,b){"object"==typeof module&&"object"==typeof module.exports?module.exports=a.document?b(a,!0):function(a){if(!a.document)throw new Error("jQuery requires a window with a document");return b(a)}:b(a)}("undefined"!=typeof window?window:this,function(a,b){var c=[],d=c.slice,e=c.concat,f=c.push,g=c.indexOf,h={},i=h.toString,j=h.hasOwnProperty,k={},l=a.document,m="2.1.4",n=function(a,b){return new n.fn.init(a,b)},o=/^[\s\uFEFF\xA0]+|[\s\uFEFF\xA0]+$/g,p=/^-ms-/,q=/-([\da-z])/gi,r=function(a,b){return b.toUpperCase()};n.fn=n.prototype={jquery:m,constructor:n,selector:"",length:0,toArray:function(){return d.call(this)},get:function(a){return null!=a?0>a?this[a+this.length]:this[a]:d.call(this)},pushStack:function(a){var b=n.merge(this.constructor(),a);return b.prevObject=this,b.context=this.context,b},each:function(a,b){return n.each(this,a,b)},map:function(a){return this.pushStack(n.map(this,function(b,c){return a.call(b,c,b)}))},slice:function(){return this.pushStack(d.apply(this,arguments))},first:function(){return this.eq(0)},last:function(){return this.eq(-1)},eq:function(a){var b=this.length,c=+a+(0>a?b:0);return this.pushStack(c>=0&&b>c?[this[c]]:[])},end:function(){return this.prevObject||this.constructor(null)},push:f,sort:c.sort,splice:c.splice},n.extend=n.fn.extend=function(){var a,b,c,d,e,f,g=arguments[0]||{},h=1,i=arguments.length,j=!1;for("boolean"==typeof g&&(j=g,g=arguments[h]||{},h++),"object"==typeof g||n.isFunction(g)||(g={}),h===i&&(g=this,h--);i>h;h++)if(null!=(a=arguments[h]))for(b in a)c=g[b],d=a[b],g!==d&&(j&&d&&(n.isPlainObject(d)||(e=n.isArray(d)))?(e?(e=!1,f=c&&n.isArray(c)?c:[]):f=c&&n.isPlainObject(c)?c:{},g[b]=n.extend(j,f,d)):void 0!==d&&(g[b]=d));return g},n.extend({expando:"jQuery"+(m+Math.random()).replace(/\D/g,""),isReady:!0,error:function(a){throw new Error(a)},noop:function(){},isFunction:function(a){return"function"===n.type(a)},isArray:Array.isArray,isWindow:function(a){return null!=a&&a===a.window},isNumeric:function(a){return!n.isArray(a)&&a-parseFloat(a)+1>=0},isPlainObject:function(a){return"object"!==n.type(a)||a.nodeType||n.isWindow(a)?!1:a.constructor&&!j.call(a.constructor.prototype,"isPrototypeOf")?!1:!0},isEmptyObject:function(a){var b;for(b in a)return!1;return!0},type:function(a){return null==a?a+"":"object"==typeof a||"function"==typeof a?h[i.call(a)]||"object":typeof a},globalEval:function(a){var b,c=eval;a=n.trim(a),a&&(1===a.indexOf("use strict")?(b=l.createElement("script"),b.text=a,l.head.appendChild(b).parentNode.removeChild(b)):c(a))},camelCase:function(a){return a.replace(p,"ms-").replace(q,r)},nodeName:function(a,b){return a.nodeName&&a.nodeName.toLowerCase()===b.toLowerCase()},each:function(a,b,c){var d,e=0,f=a.length,g=s(a);if(c){if(g){for(;f>e;e++)if(d=b.apply(a[e],c),d===!1)break}else for(e in a)if(d=b.apply(a[e],c),d===!1)break}else if(g){for(;f>e;e++)if(d=b.call(a[e],e,a[e]),d===!1)break}else for(e in a)if(d=b.call(a[e],e,a[e]),d===!1)break;return a},trim:function(a){return null==a?"":(a+"").replace(o,"")},makeArray:function(a,b){var c=b||[];return null!=a&&(s(Object(a))?n.merge(c,"string"==typeof a?[a]:a):f.call(c,a)),c},inArray:function(a,b,c){return null==b?-1:g.call(b,a,c)},merge:function(a,b){for(var c=+b.length,d=0,e=a.length;c>d;d++)a[e++]=b[d];return a.length=e,a},grep:function(a,b,c){for(var d,e=[],f=0,g=a.length,h=!c;g>f;f++)d=!b(a[f],f),d!==h&&e.push(a[f]);return e},map:function(a,b,c){var d,f=0,g=a.length,h=s(a),i=[];if(h)for(;g>f;f++)d=b(a[f],f,c),null!=d&&i.push(d);else for(f in a)d=b(a[f],f,c),null!=d&&i.push(d);return e.apply([],i)},guid:1,proxy:function(a,b){var c,e,f;return"string"==typeof b&&(c=a[b],b=a,a=c),n.isFunction(a)?(e=d.call(arguments,2),f=function(){return a.apply(b||this,e.concat(d.call(arguments)))},f.guid=a.guid=a.guid||n.guid++,f):void 0},now:Date.now,support:k}),n.each("Boolean Number String Function Array Date RegExp Object Error".split(" "),function(a,b){h["[object "+b+"]"]=b.toLowerCase()});function s(a){var b="length"in a&&a.length,c=n.type(a);return"function"===c||n.isWindow(a)?!1:1===a.nodeType&&b?!0:"array"===c||0===b||"number"==typeof b&&b>0&&b-1 in a}var t=function(a){var b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u="sizzle"+1*new Date,v=a.document,w=0,x=0,y=ha(),z=ha(),A=ha(),B=function(a,b){return a===b&&(l=!0),0},C=1<<31,D={}.hasOwnProperty,E=[],F=E.pop,G=E.push,H=E.push,I=E.slice,J=function(a,b){for(var c=0,d=a.length;d>c;c++)if(a[c]===b)return c;return-1},K="checked|selected|async|autofocus|autoplay|controls|defer|disabled|hidden|ismap|loop|multiple|open|readonly|required|scoped",L="[\\x20\\t\\r\\n\\f]",M="(?:\\\\.|[\\w-]|[^\\x00-\\xa0])+",N=M.replace("w","w#"),O="\\["+L+"*("+M+")(?:"+L+"*([*^$|!~]?=)"+L+"*(?:'((?:\\\\.|[^\\\\'])*)'|\"((?:\\\\.|[^\\\\\"])*)\"|("+N+"))|)"+L+"*\\]",P=":("+M+")(?:\\((('((?:\\\\.|[^\\\\'])*)'|\"((?:\\\\.|[^\\\\\"])*)\")|((?:\\\\.|[^\\\\()[\\]]|"+O+")*)|.*)\\)|)",Q=new RegExp(L+"+","g"),R=new RegExp("^"+L+"+|((?:^|[^\\\\])(?:\\\\.)*)"+L+"+$","g"),S=new RegExp("^"+L+"*,"+L+"*"),T=new RegExp("^"+L+"*([>+~]|"+L+")"+L+"*"),U=new RegExp("="+L+"*([^\\]'\"]*?)"+L+"*\\]","g"),V=new RegExp(P),W=new RegExp("^"+N+"$"),X={ID:new RegExp("^#("+M+")"),CLASS:new RegExp("^\\.("+M+")"),TAG:new RegExp("^("+M.replace("w","w*")+")"),ATTR:new RegExp("^"+O),PSEUDO:new RegExp("^"+P),CHILD:new RegExp("^:(only|first|last|nth|nth-last)-(child|of-type)(?:\\("+L+"*(even|odd|(([+-]|)(\\d*)n|)"+L+"*(?:([+-]|)"+L+"*(\\d+)|))"+L+"*\\)|)","i"),bool:new RegExp("^(?:"+K+")$","i"),needsContext:new RegExp("^"+L+"*[>+~]|:(even|odd|eq|gt|lt|nth|first|last)(?:\\("+L+"*((?:-\\d)?\\d*)"+L+"*\\)|)(?=[^-]|$)","i")},Y=/^(?:input|select|textarea|button)$/i,Z=/^h\d$/i,$=/^[^{]+\{\s*\[native \w/,_=/^(?:#([\w-]+)|(\w+)|\.([\w-]+))$/,aa=/[+~]/,ba=/'|\\/g,ca=new RegExp("\\\\([\\da-f]{1,6}"+L+"?|("+L+")|.)","ig"),da=function(a,b,c){var d="0x"+b-65536;return d!==d||c?b:0>d?String.fromCharCode(d+65536):String.fromCharCode(d>>10|55296,1023&d|56320)},ea=function(){m()};try{H.apply(E=I.call(v.childNodes),v.childNodes),E[v.childNodes.length].nodeType}catch(fa){H={apply:E.length?function(a,b){G.apply(a,I.call(b))}:function(a,b){var c=a.length,d=0;while(a[c++]=b[d++]);a.length=c-1}}}function ga(a,b,d,e){var f,h,j,k,l,o,r,s,w,x;if((b?b.ownerDocument||b:v)!==n&&m(b),b=b||n,d=d||[],k=b.nodeType,"string"!=typeof a||!a||1!==k&&9!==k&&11!==k)return d;if(!e&&p){if(11!==k&&(f=_.exec(a)))if(j=f[1]){if(9===k){if(h=b.getElementById(j),!h||!h.parentNode)return d;if(h.id===j)return d.push(h),d}else if(b.ownerDocument&&(h=b.ownerDocument.getElementById(j))&&t(b,h)&&h.id===j)return d.push(h),d}else{if(f[2])return H.apply(d,b.getElementsByTagName(a)),d;if((j=f[3])&&c.getElementsByClassName)return H.apply(d,b.getElementsByClassName(j)),d}if(c.qsa&&(!q||!q.test(a))){if(s=r=u,w=b,x=1!==k&&a,1===k&&"object"!==b.nodeName.toLowerCase()){o=g(a),(r=b.getAttribute("id"))?s=r.replace(ba,"\\$&"):b.setAttribute("id",s),s="[id='"+s+"'] ",l=o.length;while(l--)o[l]=s+ra(o[l]);w=aa.test(a)&&pa(b.parentNode)||b,x=o.join(",")}if(x)try{return H.apply(d,w.querySelectorAll(x)),d}catch(y){}finally{r||b.removeAttribute("id")}}}return i(a.replace(R,"$1"),b,d,e)}function ha(){var a=[];function b(c,e){return a.push(c+" ")>d.cacheLength&&delete b[a.shift()],b[c+" "]=e}return b}function ia(a){return a[u]=!0,a}function ja(a){var b=n.createElement("div");try{return!!a(b)}catch(c){return!1}finally{b.parentNode&&b.parentNode.removeChild(b),b=null}}function ka(a,b){var c=a.split("|"),e=a.length;while(e--)d.attrHandle[c[e]]=b}function la(a,b){var c=b&&a,d=c&&1===a.nodeType&&1===b.nodeType&&(~b.sourceIndex||C)-(~a.sourceIndex||C);if(d)return d;if(c)while(c=c.nextSibling)if(c===b)return-1;return a?1:-1}function ma(a){return function(b){var c=b.nodeName.toLowerCase();return"input"===c&&b.type===a}}function na(a){return function(b){var c=b.nodeName.toLowerCase();return("input"===c||"button"===c)&&b.type===a}}function oa(a){return ia(function(b){return b=+b,ia(function(c,d){var e,f=a([],c.length,b),g=f.length;while(g--)c[e=f[g]]&&(c[e]=!(d[e]=c[e]))})})}function pa(a){return a&&"undefined"!=typeof a.getElementsByTagName&&a}c=ga.support={},f=ga.isXML=function(a){var b=a&&(a.ownerDocument||a).documentElement;return b?"HTML"!==b.nodeName:!1},m=ga.setDocument=function(a){var b,e,g=a?a.ownerDocument||a:v;return g!==n&&9===g.nodeType&&g.documentElement?(n=g,o=g.documentElement,e=g.defaultView,e&&e!==e.top&&(e.addEventListener?e.addEventListener("unload",ea,!1):e.attachEvent&&e.attachEvent("onunload",ea)),p=!f(g),c.attributes=ja(function(a){return a.className="i",!a.getAttribute("className")}),c.getElementsByTagName=ja(function(a){return a.appendChild(g.createComment("")),!a.getElementsByTagName("*").length}),c.getElementsByClassName=$.test(g.getElementsByClassName),c.getById=ja(function(a){return o.appendChild(a).id=u,!g.getElementsByName||!g.getElementsByName(u).length}),c.getById?(d.find.ID=function(a,b){if("undefined"!=typeof b.getElementById&&p){var c=b.getElementById(a);return c&&c.parentNode?[c]:[]}},d.filter.ID=function(a){var b=a.replace(ca,da);return function(a){return a.getAttribute("id")===b}}):(delete d.find.ID,d.filter.ID=function(a){var b=a.replace(ca,da);return function(a){var c="undefined"!=typeof a.getAttributeNode&&a.getAttributeNode("id");return c&&c.value===b}}),d.find.TAG=c.getElementsByTagName?function(a,b){return"undefined"!=typeof b.getElementsByTagName?b.getElementsByTagName(a):c.qsa?b.querySelectorAll(a):void 0}:function(a,b){var c,d=[],e=0,f=b.getElementsByTagName(a);if("*"===a){while(c=f[e++])1===c.nodeType&&d.push(c);return d}return f},d.find.CLASS=c.getElementsByClassName&&function(a,b){return p?b.getElementsByClassName(a):void 0},r=[],q=[],(c.qsa=$.test(g.querySelectorAll))&&(ja(function(a){o.appendChild(a).innerHTML="<a id='"+u+"'></a><select id='"+u+"-\f]' msallowcapture=''><option selected=''></option></select>",a.querySelectorAll("[msallowcapture^='']").length&&q.push("[*^$]="+L+"*(?:''|\"\")"),a.querySelectorAll("[selected]").length||q.push("\\["+L+"*(?:value|"+K+")"),a.querySelectorAll("[id~="+u+"-]").length||q.push("~="),a.querySelectorAll(":checked").length||q.push(":checked"),a.querySelectorAll("a#"+u+"+*").length||q.push(".#.+[+~]")}),ja(function(a){var b=g.createElement("input");b.setAttribute("type","hidden"),a.appendChild(b).setAttribute("name","D"),a.querySelectorAll("[name=d]").length&&q.push("name"+L+"*[*^$|!~]?="),a.querySelectorAll(":enabled").length||q.push(":enabled",":disabled"),a.querySelectorAll("*,:x"),q.push(",.*:")})),(c.matchesSelector=$.test(s=o.matches||o.webkitMatchesSelector||o.mozMatchesSelector||o.oMatchesSelector||o.msMatchesSelector))&&ja(function(a){c.disconnectedMatch=s.call(a,"div"),s.call(a,"[s!='']:x"),r.push("!=",P)}),q=q.length&&new RegExp(q.join("|")),r=r.length&&new RegExp(r.join("|")),b=$.test(o.compareDocumentPosition),t=b||$.test(o.contains)?function(a,b){var c=9===a.nodeType?a.documentElement:a,d=b&&b.parentNode;return a===d||!(!d||1!==d.nodeType||!(c.contains?c.contains(d):a.compareDocumentPosition&&16&a.compareDocumentPosition(d)))}:function(a,b){if(b)while(b=b.parentNode)if(b===a)return!0;return!1},B=b?function(a,b){if(a===b)return l=!0,0;var d=!a.compareDocumentPosition-!b.compareDocumentPosition;return d?d:(d=(a.ownerDocument||a)===(b.ownerDocument||b)?a.compareDocumentPosition(b):1,1&d||!c.sortDetached&&b.compareDocumentPosition(a)===d?a===g||a.ownerDocument===v&&t(v,a)?-1:b===g||b.ownerDocument===v&&t(v,b)?1:k?J(k,a)-J(k,b):0:4&d?-1:1)}:function(a,b){if(a===b)return l=!0,0;var c,d=0,e=a.parentNode,f=b.parentNode,h=[a],i=[b];if(!e||!f)return a===g?-1:b===g?1:e?-1:f?1:k?J(k,a)-J(k,b):0;if(e===f)return la(a,b);c=a;while(c=c.parentNode)h.unshift(c);c=b;while(c=c.parentNode)i.unshift(c);while(h[d]===i[d])d++;return d?la(h[d],i[d]):h[d]===v?-1:i[d]===v?1:0},g):n},ga.matches=function(a,b){return ga(a,null,null,b)},ga.matchesSelector=function(a,b){if((a.ownerDocument||a)!==n&&m(a),b=b.replace(U,"='$1']"),!(!c.matchesSelector||!p||r&&r.test(b)||q&&q.test(b)))try{var d=s.call(a,b);if(d||c.disconnectedMatch||a.document&&11!==a.document.nodeType)return d}catch(e){}return ga(b,n,null,[a]).length>0},ga.contains=function(a,b){return(a.ownerDocument||a)!==n&&m(a),t(a,b)},ga.attr=function(a,b){(a.ownerDocument||a)!==n&&m(a);var e=d.attrHandle[b.toLowerCase()],f=e&&D.call(d.attrHandle,b.toLowerCase())?e(a,b,!p):void 0;return void 0!==f?f:c.attributes||!p?a.getAttribute(b):(f=a.getAttributeNode(b))&&f.specified?f.value:null},ga.error=function(a){throw new Error("Syntax error, unrecognized expression: "+a)},ga.uniqueSort=function(a){var b,d=[],e=0,f=0;if(l=!c.detectDuplicates,k=!c.sortStable&&a.slice(0),a.sort(B),l){while(b=a[f++])b===a[f]&&(e=d.push(f));while(e--)a.splice(d[e],1)}return k=null,a},e=ga.getText=function(a){var b,c="",d=0,f=a.nodeType;if(f){if(1===f||9===f||11===f){if("string"==typeof a.textContent)return a.textContent;for(a=a.firstChild;a;a=a.nextSibling)c+=e(a)}else if(3===f||4===f)return a.nodeValue}else while(b=a[d++])c+=e(b);return c},d=ga.selectors={cacheLength:50,createPseudo:ia,match:X,attrHandle:{},find:{},relative:{">":{dir:"parentNode",first:!0}," ":{dir:"parentNode"},"+":{dir:"previousSibling",first:!0},"~":{dir:"previousSibling"}},preFilter:{ATTR:function(a){return a[1]=a[1].replace(ca,da),a[3]=(a[3]||a[4]||a[5]||"").replace(ca,da),"~="===a[2]&&(a[3]=" "+a[3]+" "),a.slice(0,4)},CHILD:function(a){return a[1]=a[1].toLowerCase(),"nth"===a[1].slice(0,3)?(a[3]||ga.error(a[0]),a[4]=+(a[4]?a[5]+(a[6]||1):2*("even"===a[3]||"odd"===a[3])),a[5]=+(a[7]+a[8]||"odd"===a[3])):a[3]&&ga.error(a[0]),a},PSEUDO:function(a){var b,c=!a[6]&&a[2];return X.CHILD.test(a[0])?null:(a[3]?a[2]=a[4]||a[5]||"":c&&V.test(c)&&(b=g(c,!0))&&(b=c.indexOf(")",c.length-b)-c.length)&&(a[0]=a[0].slice(0,b),a[2]=c.slice(0,b)),a.slice(0,3))}},filter:{TAG:function(a){var b=a.replace(ca,da).toLowerCase();return"*"===a?function(){return!0}:function(a){return a.nodeName&&a.nodeName.toLowerCase()===b}},CLASS:function(a){var b=y[a+" "];return b||(b=new RegExp("(^|"+L+")"+a+"("+L+"|$)"))&&y(a,function(a){return b.test("string"==typeof a.className&&a.className||"undefined"!=typeof a.getAttribute&&a.getAttribute("class")||"")})},ATTR:function(a,b,c){return function(d){var e=ga.attr(d,a);return null==e?"!="===b:b?(e+="","="===b?e===c:"!="===b?e!==c:"^="===b?c&&0===e.indexOf(c):"*="===b?c&&e.indexOf(c)>-1:"$="===b?c&&e.slice(-c.length)===c:"~="===b?(" "+e.replace(Q," ")+" ").indexOf(c)>-1:"|="===b?e===c||e.slice(0,c.length+1)===c+"-":!1):!0}},CHILD:function(a,b,c,d,e){var f="nth"!==a.slice(0,3),g="last"!==a.slice(-4),h="of-type"===b;return 1===d&&0===e?function(a){return!!a.parentNode}:function(b,c,i){var j,k,l,m,n,o,p=f!==g?"nextSibling":"previousSibling",q=b.parentNode,r=h&&b.nodeName.toLowerCase(),s=!i&&!h;if(q){if(f){while(p){l=b;while(l=l[p])if(h?l.nodeName.toLowerCase()===r:1===l.nodeType)return!1;o=p="only"===a&&!o&&"nextSibling"}return!0}if(o=[g?q.firstChild:q.lastChild],g&&s){k=q[u]||(q[u]={}),j=k[a]||[],n=j[0]===w&&j[1],m=j[0]===w&&j[2],l=n&&q.childNodes[n];while(l=++n&&l&&l[p]||(m=n=0)||o.pop())if(1===l.nodeType&&++m&&l===b){k[a]=[w,n,m];break}}else if(s&&(j=(b[u]||(b[u]={}))[a])&&j[0]===w)m=j[1];else while(l=++n&&l&&l[p]||(m=n=0)||o.pop())if((h?l.nodeName.toLowerCase()===r:1===l.nodeType)&&++m&&(s&&((l[u]||(l[u]={}))[a]=[w,m]),l===b))break;return m-=e,m===d||m%d===0&&m/d>=0}}},PSEUDO:function(a,b){var c,e=d.pseudos[a]||d.setFilters[a.toLowerCase()]||ga.error("unsupported pseudo: "+a);return e[u]?e(b):e.length>1?(c=[a,a,"",b],d.setFilters.hasOwnProperty(a.toLowerCase())?ia(function(a,c){var d,f=e(a,b),g=f.length;while(g--)d=J(a,f[g]),a[d]=!(c[d]=f[g])}):function(a){return e(a,0,c)}):e}},pseudos:{not:ia(function(a){var b=[],c=[],d=h(a.replace(R,"$1"));return d[u]?ia(function(a,b,c,e){var f,g=d(a,null,e,[]),h=a.length;while(h--)(f=g[h])&&(a[h]=!(b[h]=f))}):function(a,e,f){return b[0]=a,d(b,null,f,c),b[0]=null,!c.pop()}}),has:ia(function(a){return function(b){return ga(a,b).length>0}}),contains:ia(function(a){return a=a.replace(ca,da),function(b){return(b.textContent||b.innerText||e(b)).indexOf(a)>-1}}),lang:ia(function(a){return W.test(a||"")||ga.error("unsupported lang: "+a),a=a.replace(ca,da).toLowerCase(),function(b){var c;do if(c=p?b.lang:b.getAttribute("xml:lang")||b.getAttribute("lang"))return c=c.toLowerCase(),c===a||0===c.indexOf(a+"-");while((b=b.parentNode)&&1===b.nodeType);return!1}}),target:function(b){var c=a.location&&a.location.hash;return c&&c.slice(1)===b.id},root:function(a){return a===o},focus:function(a){return a===n.activeElement&&(!n.hasFocus||n.hasFocus())&&!!(a.type||a.href||~a.tabIndex)},enabled:function(a){return a.disabled===!1},disabled:function(a){return a.disabled===!0},checked:function(a){var b=a.nodeName.toLowerCase();return"input"===b&&!!a.checked||"option"===b&&!!a.selected},selected:function(a){return a.parentNode&&a.parentNode.selectedIndex,a.selected===!0},empty:function(a){for(a=a.firstChild;a;a=a.nextSibling)if(a.nodeType<6)return!1;return!0},parent:function(a){return!d.pseudos.empty(a)},header:function(a){return Z.test(a.nodeName)},input:function(a){return Y.test(a.nodeName)},button:function(a){var b=a.nodeName.toLowerCase();return"input"===b&&"button"===a.type||"button"===b},text:function(a){var b;return"input"===a.nodeName.toLowerCase()&&"text"===a.type&&(null==(b=a.getAttribute("type"))||"text"===b.toLowerCase())},first:oa(function(){return[0]}),last:oa(function(a,b){return[b-1]}),eq:oa(function(a,b,c){return[0>c?c+b:c]}),even:oa(function(a,b){for(var c=0;b>c;c+=2)a.push(c);return a}),odd:oa(function(a,b){for(var c=1;b>c;c+=2)a.push(c);return a}),lt:oa(function(a,b,c){for(var d=0>c?c+b:c;--d>=0;)a.push(d);return a}),gt:oa(function(a,b,c){for(var d=0>c?c+b:c;++d<b;)a.push(d);return a})}},d.pseudos.nth=d.pseudos.eq;for(b in{radio:!0,checkbox:!0,file:!0,password:!0,image:!0})d.pseudos[b]=ma(b);for(b in{submit:!0,reset:!0})d.pseudos[b]=na(b);function qa(){}qa.prototype=d.filters=d.pseudos,d.setFilters=new qa,g=ga.tokenize=function(a,b){var c,e,f,g,h,i,j,k=z[a+" "];if(k)return b?0:k.slice(0);h=a,i=[],j=d.preFilter;while(h){(!c||(e=S.exec(h)))&&(e&&(h=h.slice(e[0].length)||h),i.push(f=[])),c=!1,(e=T.exec(h))&&(c=e.shift(),f.push({value:c,type:e[0].replace(R," ")}),h=h.slice(c.length));for(g in d.filter)!(e=X[g].exec(h))||j[g]&&!(e=j[g](e))||(c=e.shift(),f.push({value:c,type:g,matches:e}),h=h.slice(c.length));if(!c)break}return b?h.length:h?ga.error(a):z(a,i).slice(0)};function ra(a){for(var b=0,c=a.length,d="";c>b;b++)d+=a[b].value;return d}function sa(a,b,c){var d=b.dir,e=c&&"parentNode"===d,f=x++;return b.first?function(b,c,f){while(b=b[d])if(1===b.nodeType||e)return a(b,c,f)}:function(b,c,g){var h,i,j=[w,f];if(g){while(b=b[d])if((1===b.nodeType||e)&&a(b,c,g))return!0}else while(b=b[d])if(1===b.nodeType||e){if(i=b[u]||(b[u]={}),(h=i[d])&&h[0]===w&&h[1]===f)return j[2]=h[2];if(i[d]=j,j[2]=a(b,c,g))return!0}}}function ta(a){return a.length>1?function(b,c,d){var e=a.length;while(e--)if(!a[e](b,c,d))return!1;return!0}:a[0]}function ua(a,b,c){for(var d=0,e=b.length;e>d;d++)ga(a,b[d],c);return c}function va(a,b,c,d,e){for(var f,g=[],h=0,i=a.length,j=null!=b;i>h;h++)(f=a[h])&&(!c||c(f,d,e))&&(g.push(f),j&&b.push(h));return g}function wa(a,b,c,d,e,f){return d&&!d[u]&&(d=wa(d)),e&&!e[u]&&(e=wa(e,f)),ia(function(f,g,h,i){var j,k,l,m=[],n=[],o=g.length,p=f||ua(b||"*",h.nodeType?[h]:h,[]),q=!a||!f&&b?p:va(p,m,a,h,i),r=c?e||(f?a:o||d)?[]:g:q;if(c&&c(q,r,h,i),d){j=va(r,n),d(j,[],h,i),k=j.length;while(k--)(l=j[k])&&(r[n[k]]=!(q[n[k]]=l))}if(f){if(e||a){if(e){j=[],k=r.length;while(k--)(l=r[k])&&j.push(q[k]=l);e(null,r=[],j,i)}k=r.length;while(k--)(l=r[k])&&(j=e?J(f,l):m[k])>-1&&(f[j]=!(g[j]=l))}}else r=va(r===g?r.splice(o,r.length):r),e?e(null,g,r,i):H.apply(g,r)})}function xa(a){for(var b,c,e,f=a.length,g=d.relative[a[0].type],h=g||d.relative[" "],i=g?1:0,k=sa(function(a){return a===b},h,!0),l=sa(function(a){return J(b,a)>-1},h,!0),m=[function(a,c,d){var e=!g&&(d||c!==j)||((b=c).nodeType?k(a,c,d):l(a,c,d));return b=null,e}];f>i;i++)if(c=d.relative[a[i].type])m=[sa(ta(m),c)];else{if(c=d.filter[a[i].type].apply(null,a[i].matches),c[u]){for(e=++i;f>e;e++)if(d.relative[a[e].type])break;return wa(i>1&&ta(m),i>1&&ra(a.slice(0,i-1).concat({value:" "===a[i-2].type?"*":""})).replace(R,"$1"),c,e>i&&xa(a.slice(i,e)),f>e&&xa(a=a.slice(e)),f>e&&ra(a))}m.push(c)}return ta(m)}function ya(a,b){var c=b.length>0,e=a.length>0,f=function(f,g,h,i,k){var l,m,o,p=0,q="0",r=f&&[],s=[],t=j,u=f||e&&d.find.TAG("*",k),v=w+=null==t?1:Math.random()||.1,x=u.length;for(k&&(j=g!==n&&g);q!==x&&null!=(l=u[q]);q++){if(e&&l){m=0;while(o=a[m++])if(o(l,g,h)){i.push(l);break}k&&(w=v)}c&&((l=!o&&l)&&p--,f&&r.push(l))}if(p+=q,c&&q!==p){m=0;while(o=b[m++])o(r,s,g,h);if(f){if(p>0)while(q--)r[q]||s[q]||(s[q]=F.call(i));s=va(s)}H.apply(i,s),k&&!f&&s.length>0&&p+b.length>1&&ga.uniqueSort(i)}return k&&(w=v,j=t),r};return c?ia(f):f}return h=ga.compile=function(a,b){var c,d=[],e=[],f=A[a+" "];if(!f){b||(b=g(a)),c=b.length;while(c--)f=xa(b[c]),f[u]?d.push(f):e.push(f);f=A(a,ya(e,d)),f.selector=a}return f},i=ga.select=function(a,b,e,f){var i,j,k,l,m,n="function"==typeof a&&a,o=!f&&g(a=n.selector||a);if(e=e||[],1===o.length){if(j=o[0]=o[0].slice(0),j.length>2&&"ID"===(k=j[0]).type&&c.getById&&9===b.nodeType&&p&&d.relative[j[1].type]){if(b=(d.find.ID(k.matches[0].replace(ca,da),b)||[])[0],!b)return e;n&&(b=b.parentNode),a=a.slice(j.shift().value.length)}i=X.needsContext.test(a)?0:j.length;while(i--){if(k=j[i],d.relative[l=k.type])break;if((m=d.find[l])&&(f=m(k.matches[0].replace(ca,da),aa.test(j[0].type)&&pa(b.parentNode)||b))){if(j.splice(i,1),a=f.length&&ra(j),!a)return H.apply(e,f),e;break}}}return(n||h(a,o))(f,b,!p,e,aa.test(a)&&pa(b.parentNode)||b),e},c.sortStable=u.split("").sort(B).join("")===u,c.detectDuplicates=!!l,m(),c.sortDetached=ja(function(a){return 1&a.compareDocumentPosition(n.createElement("div"))}),ja(function(a){return a.innerHTML="<a href='#'></a>","#"===a.firstChild.getAttribute("href")})||ka("type|href|height|width",function(a,b,c){return c?void 0:a.getAttribute(b,"type"===b.toLowerCase()?1:2)}),c.attributes&&ja(function(a){return a.innerHTML="<input/>",a.firstChild.setAttribute("value",""),""===a.firstChild.getAttribute("value")})||ka("value",function(a,b,c){return c||"input"!==a.nodeName.toLowerCase()?void 0:a.defaultValue}),ja(function(a){return null==a.getAttribute("disabled")})||ka(K,function(a,b,c){var d;return c?void 0:a[b]===!0?b.toLowerCase():(d=a.getAttributeNode(b))&&d.specified?d.value:null}),ga}(a);n.find=t,n.expr=t.selectors,n.expr[":"]=n.expr.pseudos,n.unique=t.uniqueSort,n.text=t.getText,n.isXMLDoc=t.isXML,n.contains=t.contains;var u=n.expr.match.needsContext,v=/^<(\w+)\s*\/?>(?:<\/\1>|)$/,w=/^.[^:#\[\.,]*$/;function x(a,b,c){if(n.isFunction(b))return n.grep(a,function(a,d){return!!b.call(a,d,a)!==c});if(b.nodeType)return n.grep(a,function(a){return a===b!==c});if("string"==typeof b){if(w.test(b))return n.filter(b,a,c);b=n.filter(b,a)}return n.grep(a,function(a){return g.call(b,a)>=0!==c})}n.filter=function(a,b,c){var d=b[0];return c&&(a=":not("+a+")"),1===b.length&&1===d.nodeType?n.find.matchesSelector(d,a)?[d]:[]:n.find.matches(a,n.grep(b,function(a){return 1===a.nodeType}))},n.fn.extend({find:function(a){var b,c=this.length,d=[],e=this;if("string"!=typeof a)return this.pushStack(n(a).filter(function(){for(b=0;c>b;b++)if(n.contains(e[b],this))return!0}));for(b=0;c>b;b++)n.find(a,e[b],d);return d=this.pushStack(c>1?n.unique(d):d),d.selector=this.selector?this.selector+" "+a:a,d},filter:function(a){return this.pushStack(x(this,a||[],!1))},not:function(a){return this.pushStack(x(this,a||[],!0))},is:function(a){return!!x(this,"string"==typeof a&&u.test(a)?n(a):a||[],!1).length}});var y,z=/^(?:\s*(<[\w\W]+>)[^>]*|#([\w-]*))$/,A=n.fn.init=function(a,b){var c,d;if(!a)return this;if("string"==typeof a){if(c="<"===a[0]&&">"===a[a.length-1]&&a.length>=3?[null,a,null]:z.exec(a),!c||!c[1]&&b)return!b||b.jquery?(b||y).find(a):this.constructor(b).find(a);if(c[1]){if(b=b instanceof n?b[0]:b,n.merge(this,n.parseHTML(c[1],b&&b.nodeType?b.ownerDocument||b:l,!0)),v.test(c[1])&&n.isPlainObject(b))for(c in b)n.isFunction(this[c])?this[c](b[c]):this.attr(c,b[c]);return this}return d=l.getElementById(c[2]),d&&d.parentNode&&(this.length=1,this[0]=d),this.context=l,this.selector=a,this}return a.nodeType?(this.context=this[0]=a,this.length=1,this):n.isFunction(a)?"undefined"!=typeof y.ready?y.ready(a):a(n):(void 0!==a.selector&&(this.selector=a.selector,this.context=a.context),n.makeArray(a,this))};A.prototype=n.fn,y=n(l);var B=/^(?:parents|prev(?:Until|All))/,C={children:!0,contents:!0,next:!0,prev:!0};n.extend({dir:function(a,b,c){var d=[],e=void 0!==c;while((a=a[b])&&9!==a.nodeType)if(1===a.nodeType){if(e&&n(a).is(c))break;d.push(a)}return d},sibling:function(a,b){for(var c=[];a;a=a.nextSibling)1===a.nodeType&&a!==b&&c.push(a);return c}}),n.fn.extend({has:function(a){var b=n(a,this),c=b.length;return this.filter(function(){for(var a=0;c>a;a++)if(n.contains(this,b[a]))return!0})},closest:function(a,b){for(var c,d=0,e=this.length,f=[],g=u.test(a)||"string"!=typeof a?n(a,b||this.context):0;e>d;d++)for(c=this[d];c&&c!==b;c=c.parentNode)if(c.nodeType<11&&(g?g.index(c)>-1:1===c.nodeType&&n.find.matchesSelector(c,a))){f.push(c);break}return this.pushStack(f.length>1?n.unique(f):f)},index:function(a){return a?"string"==typeof a?g.call(n(a),this[0]):g.call(this,a.jquery?a[0]:a):this[0]&&this[0].parentNode?this.first().prevAll().length:-1},add:function(a,b){return this.pushStack(n.unique(n.merge(this.get(),n(a,b))))},addBack:function(a){return this.add(null==a?this.prevObject:this.prevObject.filter(a))}});function D(a,b){while((a=a[b])&&1!==a.nodeType);return a}n.each({parent:function(a){var b=a.parentNode;return b&&11!==b.nodeType?b:null},parents:function(a){return n.dir(a,"parentNode")},parentsUntil:function(a,b,c){return n.dir(a,"parentNode",c)},next:function(a){return D(a,"nextSibling")},prev:function(a){return D(a,"previousSibling")},nextAll:function(a){return n.dir(a,"nextSibling")},prevAll:function(a){return n.dir(a,"previousSibling")},nextUntil:function(a,b,c){return n.dir(a,"nextSibling",c)},prevUntil:function(a,b,c){return n.dir(a,"previousSibling",c)},siblings:function(a){return n.sibling((a.parentNode||{}).firstChild,a)},children:function(a){return n.sibling(a.firstChild)},contents:function(a){return a.contentDocument||n.merge([],a.childNodes)}},function(a,b){n.fn[a]=function(c,d){var e=n.map(this,b,c);return"Until"!==a.slice(-5)&&(d=c),d&&"string"==typeof d&&(e=n.filter(d,e)),this.length>1&&(C[a]||n.unique(e),B.test(a)&&e.reverse()),this.pushStack(e)}});var E=/\S+/g,F={};function G(a){var b=F[a]={};return n.each(a.match(E)||[],function(a,c){b[c]=!0}),b}n.Callbacks=function(a){a="string"==typeof a?F[a]||G(a):n.extend({},a);var b,c,d,e,f,g,h=[],i=!a.once&&[],j=function(l){for(b=a.memory&&l,c=!0,g=e||0,e=0,f=h.length,d=!0;h&&f>g;g++)if(h[g].apply(l[0],l[1])===!1&&a.stopOnFalse){b=!1;break}d=!1,h&&(i?i.length&&j(i.shift()):b?h=[]:k.disable())},k={add:function(){if(h){var c=h.length;!function g(b){n.each(b,function(b,c){var d=n.type(c);"function"===d?a.unique&&k.has(c)||h.push(c):c&&c.length&&"string"!==d&&g(c)})}(arguments),d?f=h.length:b&&(e=c,j(b))}return this},remove:function(){return h&&n.each(arguments,function(a,b){var c;while((c=n.inArray(b,h,c))>-1)h.splice(c,1),d&&(f>=c&&f--,g>=c&&g--)}),this},has:function(a){return a?n.inArray(a,h)>-1:!(!h||!h.length)},empty:function(){return h=[],f=0,this},disable:function(){return h=i=b=void 0,this},disabled:function(){return!h},lock:function(){return i=void 0,b||k.disable(),this},locked:function(){return!i},fireWith:function(a,b){return!h||c&&!i||(b=b||[],b=[a,b.slice?b.slice():b],d?i.push(b):j(b)),this},fire:function(){return k.fireWith(this,arguments),this},fired:function(){return!!c}};return k},n.extend({Deferred:function(a){var b=[["resolve","done",n.Callbacks("once memory"),"resolved"],["reject","fail",n.Callbacks("once memory"),"rejected"],["notify","progress",n.Callbacks("memory")]],c="pending",d={state:function(){return c},always:function(){return e.done(arguments).fail(arguments),this},then:function(){var a=arguments;return n.Deferred(function(c){n.each(b,function(b,f){var g=n.isFunction(a[b])&&a[b];e[f[1]](function(){var a=g&&g.apply(this,arguments);a&&n.isFunction(a.promise)?a.promise().done(c.resolve).fail(c.reject).progress(c.notify):c[f[0]+"With"](this===d?c.promise():this,g?[a]:arguments)})}),a=null}).promise()},promise:function(a){return null!=a?n.extend(a,d):d}},e={};return d.pipe=d.then,n.each(b,function(a,f){var g=f[2],h=f[3];d[f[1]]=g.add,h&&g.add(function(){c=h},b[1^a][2].disable,b[2][2].lock),e[f[0]]=function(){return e[f[0]+"With"](this===e?d:this,arguments),this},e[f[0]+"With"]=g.fireWith}),d.promise(e),a&&a.call(e,e),e},when:function(a){var b=0,c=d.call(arguments),e=c.length,f=1!==e||a&&n.isFunction(a.promise)?e:0,g=1===f?a:n.Deferred(),h=function(a,b,c){return function(e){b[a]=this,c[a]=arguments.length>1?d.call(arguments):e,c===i?g.notifyWith(b,c):--f||g.resolveWith(b,c)}},i,j,k;if(e>1)for(i=new Array(e),j=new Array(e),k=new Array(e);e>b;b++)c[b]&&n.isFunction(c[b].promise)?c[b].promise().done(h(b,k,c)).fail(g.reject).progress(h(b,j,i)):--f;return f||g.resolveWith(k,c),g.promise()}});var H;n.fn.ready=function(a){return n.ready.promise().done(a),this},n.extend({isReady:!1,readyWait:1,holdReady:function(a){a?n.readyWait++:n.ready(!0)},ready:function(a){(a===!0?--n.readyWait:n.isReady)||(n.isReady=!0,a!==!0&&--n.readyWait>0||(H.resolveWith(l,[n]),n.fn.triggerHandler&&(n(l).triggerHandler("ready"),n(l).off("ready"))))}});function I(){l.removeEventListener("DOMContentLoaded",I,!1),a.removeEventListener("load",I,!1),n.ready()}n.ready.promise=function(b){return H||(H=n.Deferred(),"complete"===l.readyState?setTimeout(n.ready):(l.addEventListener("DOMContentLoaded",I,!1),a.addEventListener("load",I,!1))),H.promise(b)},n.ready.promise();var J=n.access=function(a,b,c,d,e,f,g){var h=0,i=a.length,j=null==c;if("object"===n.type(c)){e=!0;for(h in c)n.access(a,b,h,c[h],!0,f,g)}else if(void 0!==d&&(e=!0,n.isFunction(d)||(g=!0),j&&(g?(b.call(a,d),b=null):(j=b,b=function(a,b,c){return j.call(n(a),c)})),b))for(;i>h;h++)b(a[h],c,g?d:d.call(a[h],h,b(a[h],c)));return e?a:j?b.call(a):i?b(a[0],c):f};n.acceptData=function(a){return 1===a.nodeType||9===a.nodeType||!+a.nodeType};function K(){Object.defineProperty(this.cache={},0,{get:function(){return{}}}),this.expando=n.expando+K.uid++}K.uid=1,K.accepts=n.acceptData,K.prototype={key:function(a){if(!K.accepts(a))return 0;var b={},c=a[this.expando];if(!c){c=K.uid++;try{b[this.expando]={value:c},Object.defineProperties(a,b)}catch(d){b[this.expando]=c,n.extend(a,b)}}return this.cache[c]||(this.cache[c]={}),c},set:function(a,b,c){var d,e=this.key(a),f=this.cache[e];if("string"==typeof b)f[b]=c;else if(n.isEmptyObject(f))n.extend(this.cache[e],b);else for(d in b)f[d]=b[d];return f},get:function(a,b){var c=this.cache[this.key(a)];return void 0===b?c:c[b]},access:function(a,b,c){var d;return void 0===b||b&&"string"==typeof b&&void 0===c?(d=this.get(a,b),void 0!==d?d:this.get(a,n.camelCase(b))):(this.set(a,b,c),void 0!==c?c:b)},remove:function(a,b){var c,d,e,f=this.key(a),g=this.cache[f];if(void 0===b)this.cache[f]={};else{n.isArray(b)?d=b.concat(b.map(n.camelCase)):(e=n.camelCase(b),b in g?d=[b,e]:(d=e,d=d in g?[d]:d.match(E)||[])),c=d.length;while(c--)delete g[d[c]]}},hasData:function(a){return!n.isEmptyObject(this.cache[a[this.expando]]||{})},discard:function(a){a[this.expando]&&delete this.cache[a[this.expando]]}};var L=new K,M=new K,N=/^(?:\{[\w\W]*\}|\[[\w\W]*\])$/,O=/([A-Z])/g;function P(a,b,c){var d;if(void 0===c&&1===a.nodeType)if(d="data-"+b.replace(O,"-$1").toLowerCase(),c=a.getAttribute(d),"string"==typeof c){try{c="true"===c?!0:"false"===c?!1:"null"===c?null:+c+""===c?+c:N.test(c)?n.parseJSON(c):c}catch(e){}M.set(a,b,c)}else c=void 0;return c}n.extend({hasData:function(a){return M.hasData(a)||L.hasData(a)},data:function(a,b,c){
return M.access(a,b,c)},removeData:function(a,b){M.remove(a,b)},_data:function(a,b,c){return L.access(a,b,c)},_removeData:function(a,b){L.remove(a,b)}}),n.fn.extend({data:function(a,b){var c,d,e,f=this[0],g=f&&f.attributes;if(void 0===a){if(this.length&&(e=M.get(f),1===f.nodeType&&!L.get(f,"hasDataAttrs"))){c=g.length;while(c--)g[c]&&(d=g[c].name,0===d.indexOf("data-")&&(d=n.camelCase(d.slice(5)),P(f,d,e[d])));L.set(f,"hasDataAttrs",!0)}return e}return"object"==typeof a?this.each(function(){M.set(this,a)}):J(this,function(b){var c,d=n.camelCase(a);if(f&&void 0===b){if(c=M.get(f,a),void 0!==c)return c;if(c=M.get(f,d),void 0!==c)return c;if(c=P(f,d,void 0),void 0!==c)return c}else this.each(function(){var c=M.get(this,d);M.set(this,d,b),-1!==a.indexOf("-")&&void 0!==c&&M.set(this,a,b)})},null,b,arguments.length>1,null,!0)},removeData:function(a){return this.each(function(){M.remove(this,a)})}}),n.extend({queue:function(a,b,c){var d;return a?(b=(b||"fx")+"queue",d=L.get(a,b),c&&(!d||n.isArray(c)?d=L.access(a,b,n.makeArray(c)):d.push(c)),d||[]):void 0},dequeue:function(a,b){b=b||"fx";var c=n.queue(a,b),d=c.length,e=c.shift(),f=n._queueHooks(a,b),g=function(){n.dequeue(a,b)};"inprogress"===e&&(e=c.shift(),d--),e&&("fx"===b&&c.unshift("inprogress"),delete f.stop,e.call(a,g,f)),!d&&f&&f.empty.fire()},_queueHooks:function(a,b){var c=b+"queueHooks";return L.get(a,c)||L.access(a,c,{empty:n.Callbacks("once memory").add(function(){L.remove(a,[b+"queue",c])})})}}),n.fn.extend({queue:function(a,b){var c=2;return"string"!=typeof a&&(b=a,a="fx",c--),arguments.length<c?n.queue(this[0],a):void 0===b?this:this.each(function(){var c=n.queue(this,a,b);n._queueHooks(this,a),"fx"===a&&"inprogress"!==c[0]&&n.dequeue(this,a)})},dequeue:function(a){return this.each(function(){n.dequeue(this,a)})},clearQueue:function(a){return this.queue(a||"fx",[])},promise:function(a,b){var c,d=1,e=n.Deferred(),f=this,g=this.length,h=function(){--d||e.resolveWith(f,[f])};"string"!=typeof a&&(b=a,a=void 0),a=a||"fx";while(g--)c=L.get(f[g],a+"queueHooks"),c&&c.empty&&(d++,c.empty.add(h));return h(),e.promise(b)}});var Q=/[+-]?(?:\d*\.|)\d+(?:[eE][+-]?\d+|)/.source,R=["Top","Right","Bottom","Left"],S=function(a,b){return a=b||a,"none"===n.css(a,"display")||!n.contains(a.ownerDocument,a)},T=/^(?:checkbox|radio)$/i;!function(){var a=l.createDocumentFragment(),b=a.appendChild(l.createElement("div")),c=l.createElement("input");c.setAttribute("type","radio"),c.setAttribute("checked","checked"),c.setAttribute("name","t"),b.appendChild(c),k.checkClone=b.cloneNode(!0).cloneNode(!0).lastChild.checked,b.innerHTML="<textarea>x</textarea>",k.noCloneChecked=!!b.cloneNode(!0).lastChild.defaultValue}();var U="undefined";k.focusinBubbles="onfocusin"in a;var V=/^key/,W=/^(?:mouse|pointer|contextmenu)|click/,X=/^(?:focusinfocus|focusoutblur)$/,Y=/^([^.]*)(?:\.(.+)|)$/;function Z(){return!0}function $(){return!1}function _(){try{return l.activeElement}catch(a){}}n.event={global:{},add:function(a,b,c,d,e){var f,g,h,i,j,k,l,m,o,p,q,r=L.get(a);if(r){c.handler&&(f=c,c=f.handler,e=f.selector),c.guid||(c.guid=n.guid++),(i=r.events)||(i=r.events={}),(g=r.handle)||(g=r.handle=function(b){return typeof n!==U&&n.event.triggered!==b.type?n.event.dispatch.apply(a,arguments):void 0}),b=(b||"").match(E)||[""],j=b.length;while(j--)h=Y.exec(b[j])||[],o=q=h[1],p=(h[2]||"").split(".").sort(),o&&(l=n.event.special[o]||{},o=(e?l.delegateType:l.bindType)||o,l=n.event.special[o]||{},k=n.extend({type:o,origType:q,data:d,handler:c,guid:c.guid,selector:e,needsContext:e&&n.expr.match.needsContext.test(e),namespace:p.join(".")},f),(m=i[o])||(m=i[o]=[],m.delegateCount=0,l.setup&&l.setup.call(a,d,p,g)!==!1||a.addEventListener&&a.addEventListener(o,g,!1)),l.add&&(l.add.call(a,k),k.handler.guid||(k.handler.guid=c.guid)),e?m.splice(m.delegateCount++,0,k):m.push(k),n.event.global[o]=!0)}},remove:function(a,b,c,d,e){var f,g,h,i,j,k,l,m,o,p,q,r=L.hasData(a)&&L.get(a);if(r&&(i=r.events)){b=(b||"").match(E)||[""],j=b.length;while(j--)if(h=Y.exec(b[j])||[],o=q=h[1],p=(h[2]||"").split(".").sort(),o){l=n.event.special[o]||{},o=(d?l.delegateType:l.bindType)||o,m=i[o]||[],h=h[2]&&new RegExp("(^|\\.)"+p.join("\\.(?:.*\\.|)")+"(\\.|$)"),g=f=m.length;while(f--)k=m[f],!e&&q!==k.origType||c&&c.guid!==k.guid||h&&!h.test(k.namespace)||d&&d!==k.selector&&("**"!==d||!k.selector)||(m.splice(f,1),k.selector&&m.delegateCount--,l.remove&&l.remove.call(a,k));g&&!m.length&&(l.teardown&&l.teardown.call(a,p,r.handle)!==!1||n.removeEvent(a,o,r.handle),delete i[o])}else for(o in i)n.event.remove(a,o+b[j],c,d,!0);n.isEmptyObject(i)&&(delete r.handle,L.remove(a,"events"))}},trigger:function(b,c,d,e){var f,g,h,i,k,m,o,p=[d||l],q=j.call(b,"type")?b.type:b,r=j.call(b,"namespace")?b.namespace.split("."):[];if(g=h=d=d||l,3!==d.nodeType&&8!==d.nodeType&&!X.test(q+n.event.triggered)&&(q.indexOf(".")>=0&&(r=q.split("."),q=r.shift(),r.sort()),k=q.indexOf(":")<0&&"on"+q,b=b[n.expando]?b:new n.Event(q,"object"==typeof b&&b),b.isTrigger=e?2:3,b.namespace=r.join("."),b.namespace_re=b.namespace?new RegExp("(^|\\.)"+r.join("\\.(?:.*\\.|)")+"(\\.|$)"):null,b.result=void 0,b.target||(b.target=d),c=null==c?[b]:n.makeArray(c,[b]),o=n.event.special[q]||{},e||!o.trigger||o.trigger.apply(d,c)!==!1)){if(!e&&!o.noBubble&&!n.isWindow(d)){for(i=o.delegateType||q,X.test(i+q)||(g=g.parentNode);g;g=g.parentNode)p.push(g),h=g;h===(d.ownerDocument||l)&&p.push(h.defaultView||h.parentWindow||a)}f=0;while((g=p[f++])&&!b.isPropagationStopped())b.type=f>1?i:o.bindType||q,m=(L.get(g,"events")||{})[b.type]&&L.get(g,"handle"),m&&m.apply(g,c),m=k&&g[k],m&&m.apply&&n.acceptData(g)&&(b.result=m.apply(g,c),b.result===!1&&b.preventDefault());return b.type=q,e||b.isDefaultPrevented()||o._default&&o._default.apply(p.pop(),c)!==!1||!n.acceptData(d)||k&&n.isFunction(d[q])&&!n.isWindow(d)&&(h=d[k],h&&(d[k]=null),n.event.triggered=q,d[q](),n.event.triggered=void 0,h&&(d[k]=h)),b.result}},dispatch:function(a){a=n.event.fix(a);var b,c,e,f,g,h=[],i=d.call(arguments),j=(L.get(this,"events")||{})[a.type]||[],k=n.event.special[a.type]||{};if(i[0]=a,a.delegateTarget=this,!k.preDispatch||k.preDispatch.call(this,a)!==!1){h=n.event.handlers.call(this,a,j),b=0;while((f=h[b++])&&!a.isPropagationStopped()){a.currentTarget=f.elem,c=0;while((g=f.handlers[c++])&&!a.isImmediatePropagationStopped())(!a.namespace_re||a.namespace_re.test(g.namespace))&&(a.handleObj=g,a.data=g.data,e=((n.event.special[g.origType]||{}).handle||g.handler).apply(f.elem,i),void 0!==e&&(a.result=e)===!1&&(a.preventDefault(),a.stopPropagation()))}return k.postDispatch&&k.postDispatch.call(this,a),a.result}},handlers:function(a,b){var c,d,e,f,g=[],h=b.delegateCount,i=a.target;if(h&&i.nodeType&&(!a.button||"click"!==a.type))for(;i!==this;i=i.parentNode||this)if(i.disabled!==!0||"click"!==a.type){for(d=[],c=0;h>c;c++)f=b[c],e=f.selector+" ",void 0===d[e]&&(d[e]=f.needsContext?n(e,this).index(i)>=0:n.find(e,this,null,[i]).length),d[e]&&d.push(f);d.length&&g.push({elem:i,handlers:d})}return h<b.length&&g.push({elem:this,handlers:b.slice(h)}),g},props:"altKey bubbles cancelable ctrlKey currentTarget eventPhase metaKey relatedTarget shiftKey target timeStamp view which".split(" "),fixHooks:{},keyHooks:{props:"char charCode key keyCode".split(" "),filter:function(a,b){return null==a.which&&(a.which=null!=b.charCode?b.charCode:b.keyCode),a}},mouseHooks:{props:"button buttons clientX clientY offsetX offsetY pageX pageY screenX screenY toElement".split(" "),filter:function(a,b){var c,d,e,f=b.button;return null==a.pageX&&null!=b.clientX&&(c=a.target.ownerDocument||l,d=c.documentElement,e=c.body,a.pageX=b.clientX+(d&&d.scrollLeft||e&&e.scrollLeft||0)-(d&&d.clientLeft||e&&e.clientLeft||0),a.pageY=b.clientY+(d&&d.scrollTop||e&&e.scrollTop||0)-(d&&d.clientTop||e&&e.clientTop||0)),a.which||void 0===f||(a.which=1&f?1:2&f?3:4&f?2:0),a}},fix:function(a){if(a[n.expando])return a;var b,c,d,e=a.type,f=a,g=this.fixHooks[e];g||(this.fixHooks[e]=g=W.test(e)?this.mouseHooks:V.test(e)?this.keyHooks:{}),d=g.props?this.props.concat(g.props):this.props,a=new n.Event(f),b=d.length;while(b--)c=d[b],a[c]=f[c];return a.target||(a.target=l),3===a.target.nodeType&&(a.target=a.target.parentNode),g.filter?g.filter(a,f):a},special:{load:{noBubble:!0},focus:{trigger:function(){return this!==_()&&this.focus?(this.focus(),!1):void 0},delegateType:"focusin"},blur:{trigger:function(){return this===_()&&this.blur?(this.blur(),!1):void 0},delegateType:"focusout"},click:{trigger:function(){return"checkbox"===this.type&&this.click&&n.nodeName(this,"input")?(this.click(),!1):void 0},_default:function(a){return n.nodeName(a.target,"a")}},beforeunload:{postDispatch:function(a){void 0!==a.result&&a.originalEvent&&(a.originalEvent.returnValue=a.result)}}},simulate:function(a,b,c,d){var e=n.extend(new n.Event,c,{type:a,isSimulated:!0,originalEvent:{}});d?n.event.trigger(e,null,b):n.event.dispatch.call(b,e),e.isDefaultPrevented()&&c.preventDefault()}},n.removeEvent=function(a,b,c){a.removeEventListener&&a.removeEventListener(b,c,!1)},n.Event=function(a,b){return this instanceof n.Event?(a&&a.type?(this.originalEvent=a,this.type=a.type,this.isDefaultPrevented=a.defaultPrevented||void 0===a.defaultPrevented&&a.returnValue===!1?Z:$):this.type=a,b&&n.extend(this,b),this.timeStamp=a&&a.timeStamp||n.now(),void(this[n.expando]=!0)):new n.Event(a,b)},n.Event.prototype={isDefaultPrevented:$,isPropagationStopped:$,isImmediatePropagationStopped:$,preventDefault:function(){var a=this.originalEvent;this.isDefaultPrevented=Z,a&&a.preventDefault&&a.preventDefault()},stopPropagation:function(){var a=this.originalEvent;this.isPropagationStopped=Z,a&&a.stopPropagation&&a.stopPropagation()},stopImmediatePropagation:function(){var a=this.originalEvent;this.isImmediatePropagationStopped=Z,a&&a.stopImmediatePropagation&&a.stopImmediatePropagation(),this.stopPropagation()}},n.each({mouseenter:"mouseover",mouseleave:"mouseout",pointerenter:"pointerover",pointerleave:"pointerout"},function(a,b){n.event.special[a]={delegateType:b,bindType:b,handle:function(a){var c,d=this,e=a.relatedTarget,f=a.handleObj;return(!e||e!==d&&!n.contains(d,e))&&(a.type=f.origType,c=f.handler.apply(this,arguments),a.type=b),c}}}),k.focusinBubbles||n.each({focus:"focusin",blur:"focusout"},function(a,b){var c=function(a){n.event.simulate(b,a.target,n.event.fix(a),!0)};n.event.special[b]={setup:function(){var d=this.ownerDocument||this,e=L.access(d,b);e||d.addEventListener(a,c,!0),L.access(d,b,(e||0)+1)},teardown:function(){var d=this.ownerDocument||this,e=L.access(d,b)-1;e?L.access(d,b,e):(d.removeEventListener(a,c,!0),L.remove(d,b))}}}),n.fn.extend({on:function(a,b,c,d,e){var f,g;if("object"==typeof a){"string"!=typeof b&&(c=c||b,b=void 0);for(g in a)this.on(g,b,c,a[g],e);return this}if(null==c&&null==d?(d=b,c=b=void 0):null==d&&("string"==typeof b?(d=c,c=void 0):(d=c,c=b,b=void 0)),d===!1)d=$;else if(!d)return this;return 1===e&&(f=d,d=function(a){return n().off(a),f.apply(this,arguments)},d.guid=f.guid||(f.guid=n.guid++)),this.each(function(){n.event.add(this,a,d,c,b)})},one:function(a,b,c,d){return this.on(a,b,c,d,1)},off:function(a,b,c){var d,e;if(a&&a.preventDefault&&a.handleObj)return d=a.handleObj,n(a.delegateTarget).off(d.namespace?d.origType+"."+d.namespace:d.origType,d.selector,d.handler),this;if("object"==typeof a){for(e in a)this.off(e,b,a[e]);return this}return(b===!1||"function"==typeof b)&&(c=b,b=void 0),c===!1&&(c=$),this.each(function(){n.event.remove(this,a,c,b)})},trigger:function(a,b){return this.each(function(){n.event.trigger(a,b,this)})},triggerHandler:function(a,b){var c=this[0];return c?n.event.trigger(a,b,c,!0):void 0}});var aa=/<(?!area|br|col|embed|hr|img|input|link|meta|param)(([\w:]+)[^>]*)\/>/gi,ba=/<([\w:]+)/,ca=/<|&#?\w+;/,da=/<(?:script|style|link)/i,ea=/checked\s*(?:[^=]|=\s*.checked.)/i,fa=/^$|\/(?:java|ecma)script/i,ga=/^true\/(.*)/,ha=/^\s*<!(?:\[CDATA\[|--)|(?:\]\]|--)>\s*$/g,ia={option:[1,"<select multiple='multiple'>","</select>"],thead:[1,"<table>","</table>"],col:[2,"<table><colgroup>","</colgroup></table>"],tr:[2,"<table><tbody>","</tbody></table>"],td:[3,"<table><tbody><tr>","</tr></tbody></table>"],_default:[0,"",""]};ia.optgroup=ia.option,ia.tbody=ia.tfoot=ia.colgroup=ia.caption=ia.thead,ia.th=ia.td;function ja(a,b){return n.nodeName(a,"table")&&n.nodeName(11!==b.nodeType?b:b.firstChild,"tr")?a.getElementsByTagName("tbody")[0]||a.appendChild(a.ownerDocument.createElement("tbody")):a}function ka(a){return a.type=(null!==a.getAttribute("type"))+"/"+a.type,a}function la(a){var b=ga.exec(a.type);return b?a.type=b[1]:a.removeAttribute("type"),a}function ma(a,b){for(var c=0,d=a.length;d>c;c++)L.set(a[c],"globalEval",!b||L.get(b[c],"globalEval"))}function na(a,b){var c,d,e,f,g,h,i,j;if(1===b.nodeType){if(L.hasData(a)&&(f=L.access(a),g=L.set(b,f),j=f.events)){delete g.handle,g.events={};for(e in j)for(c=0,d=j[e].length;d>c;c++)n.event.add(b,e,j[e][c])}M.hasData(a)&&(h=M.access(a),i=n.extend({},h),M.set(b,i))}}function oa(a,b){var c=a.getElementsByTagName?a.getElementsByTagName(b||"*"):a.querySelectorAll?a.querySelectorAll(b||"*"):[];return void 0===b||b&&n.nodeName(a,b)?n.merge([a],c):c}function pa(a,b){var c=b.nodeName.toLowerCase();"input"===c&&T.test(a.type)?b.checked=a.checked:("input"===c||"textarea"===c)&&(b.defaultValue=a.defaultValue)}n.extend({clone:function(a,b,c){var d,e,f,g,h=a.cloneNode(!0),i=n.contains(a.ownerDocument,a);if(!(k.noCloneChecked||1!==a.nodeType&&11!==a.nodeType||n.isXMLDoc(a)))for(g=oa(h),f=oa(a),d=0,e=f.length;e>d;d++)pa(f[d],g[d]);if(b)if(c)for(f=f||oa(a),g=g||oa(h),d=0,e=f.length;e>d;d++)na(f[d],g[d]);else na(a,h);return g=oa(h,"script"),g.length>0&&ma(g,!i&&oa(a,"script")),h},buildFragment:function(a,b,c,d){for(var e,f,g,h,i,j,k=b.createDocumentFragment(),l=[],m=0,o=a.length;o>m;m++)if(e=a[m],e||0===e)if("object"===n.type(e))n.merge(l,e.nodeType?[e]:e);else if(ca.test(e)){f=f||k.appendChild(b.createElement("div")),g=(ba.exec(e)||["",""])[1].toLowerCase(),h=ia[g]||ia._default,f.innerHTML=h[1]+e.replace(aa,"<$1></$2>")+h[2],j=h[0];while(j--)f=f.lastChild;n.merge(l,f.childNodes),f=k.firstChild,f.textContent=""}else l.push(b.createTextNode(e));k.textContent="",m=0;while(e=l[m++])if((!d||-1===n.inArray(e,d))&&(i=n.contains(e.ownerDocument,e),f=oa(k.appendChild(e),"script"),i&&ma(f),c)){j=0;while(e=f[j++])fa.test(e.type||"")&&c.push(e)}return k},cleanData:function(a){for(var b,c,d,e,f=n.event.special,g=0;void 0!==(c=a[g]);g++){if(n.acceptData(c)&&(e=c[L.expando],e&&(b=L.cache[e]))){if(b.events)for(d in b.events)f[d]?n.event.remove(c,d):n.removeEvent(c,d,b.handle);L.cache[e]&&delete L.cache[e]}delete M.cache[c[M.expando]]}}}),n.fn.extend({text:function(a){return J(this,function(a){return void 0===a?n.text(this):this.empty().each(function(){(1===this.nodeType||11===this.nodeType||9===this.nodeType)&&(this.textContent=a)})},null,a,arguments.length)},append:function(){return this.domManip(arguments,function(a){if(1===this.nodeType||11===this.nodeType||9===this.nodeType){var b=ja(this,a);b.appendChild(a)}})},prepend:function(){return this.domManip(arguments,function(a){if(1===this.nodeType||11===this.nodeType||9===this.nodeType){var b=ja(this,a);b.insertBefore(a,b.firstChild)}})},before:function(){return this.domManip(arguments,function(a){this.parentNode&&this.parentNode.insertBefore(a,this)})},after:function(){return this.domManip(arguments,function(a){this.parentNode&&this.parentNode.insertBefore(a,this.nextSibling)})},remove:function(a,b){for(var c,d=a?n.filter(a,this):this,e=0;null!=(c=d[e]);e++)b||1!==c.nodeType||n.cleanData(oa(c)),c.parentNode&&(b&&n.contains(c.ownerDocument,c)&&ma(oa(c,"script")),c.parentNode.removeChild(c));return this},empty:function(){for(var a,b=0;null!=(a=this[b]);b++)1===a.nodeType&&(n.cleanData(oa(a,!1)),a.textContent="");return this},clone:function(a,b){return a=null==a?!1:a,b=null==b?a:b,this.map(function(){return n.clone(this,a,b)})},html:function(a){return J(this,function(a){var b=this[0]||{},c=0,d=this.length;if(void 0===a&&1===b.nodeType)return b.innerHTML;if("string"==typeof a&&!da.test(a)&&!ia[(ba.exec(a)||["",""])[1].toLowerCase()]){a=a.replace(aa,"<$1></$2>");try{for(;d>c;c++)b=this[c]||{},1===b.nodeType&&(n.cleanData(oa(b,!1)),b.innerHTML=a);b=0}catch(e){}}b&&this.empty().append(a)},null,a,arguments.length)},replaceWith:function(){var a=arguments[0];return this.domManip(arguments,function(b){a=this.parentNode,n.cleanData(oa(this)),a&&a.replaceChild(b,this)}),a&&(a.length||a.nodeType)?this:this.remove()},detach:function(a){return this.remove(a,!0)},domManip:function(a,b){a=e.apply([],a);var c,d,f,g,h,i,j=0,l=this.length,m=this,o=l-1,p=a[0],q=n.isFunction(p);if(q||l>1&&"string"==typeof p&&!k.checkClone&&ea.test(p))return this.each(function(c){var d=m.eq(c);q&&(a[0]=p.call(this,c,d.html())),d.domManip(a,b)});if(l&&(c=n.buildFragment(a,this[0].ownerDocument,!1,this),d=c.firstChild,1===c.childNodes.length&&(c=d),d)){for(f=n.map(oa(c,"script"),ka),g=f.length;l>j;j++)h=c,j!==o&&(h=n.clone(h,!0,!0),g&&n.merge(f,oa(h,"script"))),b.call(this[j],h,j);if(g)for(i=f[f.length-1].ownerDocument,n.map(f,la),j=0;g>j;j++)h=f[j],fa.test(h.type||"")&&!L.access(h,"globalEval")&&n.contains(i,h)&&(h.src?n._evalUrl&&n._evalUrl(h.src):n.globalEval(h.textContent.replace(ha,"")))}return this}}),n.each({appendTo:"append",prependTo:"prepend",insertBefore:"before",insertAfter:"after",replaceAll:"replaceWith"},function(a,b){n.fn[a]=function(a){for(var c,d=[],e=n(a),g=e.length-1,h=0;g>=h;h++)c=h===g?this:this.clone(!0),n(e[h])[b](c),f.apply(d,c.get());return this.pushStack(d)}});var qa,ra={};function sa(b,c){var d,e=n(c.createElement(b)).appendTo(c.body),f=a.getDefaultComputedStyle&&(d=a.getDefaultComputedStyle(e[0]))?d.display:n.css(e[0],"display");return e.detach(),f}function ta(a){var b=l,c=ra[a];return c||(c=sa(a,b),"none"!==c&&c||(qa=(qa||n("<iframe frameborder='0' width='0' height='0'/>")).appendTo(b.documentElement),b=qa[0].contentDocument,b.write(),b.close(),c=sa(a,b),qa.detach()),ra[a]=c),c}var ua=/^margin/,va=new RegExp("^("+Q+")(?!px)[a-z%]+$","i"),wa=function(b){return b.ownerDocument.defaultView.opener?b.ownerDocument.defaultView.getComputedStyle(b,null):a.getComputedStyle(b,null)};function xa(a,b,c){var d,e,f,g,h=a.style;return c=c||wa(a),c&&(g=c.getPropertyValue(b)||c[b]),c&&(""!==g||n.contains(a.ownerDocument,a)||(g=n.style(a,b)),va.test(g)&&ua.test(b)&&(d=h.width,e=h.minWidth,f=h.maxWidth,h.minWidth=h.maxWidth=h.width=g,g=c.width,h.width=d,h.minWidth=e,h.maxWidth=f)),void 0!==g?g+"":g}function ya(a,b){return{get:function(){return a()?void delete this.get:(this.get=b).apply(this,arguments)}}}!function(){var b,c,d=l.documentElement,e=l.createElement("div"),f=l.createElement("div");if(f.style){f.style.backgroundClip="content-box",f.cloneNode(!0).style.backgroundClip="",k.clearCloneStyle="content-box"===f.style.backgroundClip,e.style.cssText="border:0;width:0;height:0;top:0;left:-9999px;margin-top:1px;position:absolute",e.appendChild(f);function g(){f.style.cssText="-webkit-box-sizing:border-box;-moz-box-sizing:border-box;box-sizing:border-box;display:block;margin-top:1%;top:1%;border:1px;padding:1px;width:4px;position:absolute",f.innerHTML="",d.appendChild(e);var g=a.getComputedStyle(f,null);b="1%"!==g.top,c="4px"===g.width,d.removeChild(e)}a.getComputedStyle&&n.extend(k,{pixelPosition:function(){return g(),b},boxSizingReliable:function(){return null==c&&g(),c},reliableMarginRight:function(){var b,c=f.appendChild(l.createElement("div"));return c.style.cssText=f.style.cssText="-webkit-box-sizing:content-box;-moz-box-sizing:content-box;box-sizing:content-box;display:block;margin:0;border:0;padding:0",c.style.marginRight=c.style.width="0",f.style.width="1px",d.appendChild(e),b=!parseFloat(a.getComputedStyle(c,null).marginRight),d.removeChild(e),f.removeChild(c),b}})}}(),n.swap=function(a,b,c,d){var e,f,g={};for(f in b)g[f]=a.style[f],a.style[f]=b[f];e=c.apply(a,d||[]);for(f in b)a.style[f]=g[f];return e};var za=/^(none|table(?!-c[ea]).+)/,Aa=new RegExp("^("+Q+")(.*)$","i"),Ba=new RegExp("^([+-])=("+Q+")","i"),Ca={position:"absolute",visibility:"hidden",display:"block"},Da={letterSpacing:"0",fontWeight:"400"},Ea=["Webkit","O","Moz","ms"];function Fa(a,b){if(b in a)return b;var c=b[0].toUpperCase()+b.slice(1),d=b,e=Ea.length;while(e--)if(b=Ea[e]+c,b in a)return b;return d}function Ga(a,b,c){var d=Aa.exec(b);return d?Math.max(0,d[1]-(c||0))+(d[2]||"px"):b}function Ha(a,b,c,d,e){for(var f=c===(d?"border":"content")?4:"width"===b?1:0,g=0;4>f;f+=2)"margin"===c&&(g+=n.css(a,c+R[f],!0,e)),d?("content"===c&&(g-=n.css(a,"padding"+R[f],!0,e)),"margin"!==c&&(g-=n.css(a,"border"+R[f]+"Width",!0,e))):(g+=n.css(a,"padding"+R[f],!0,e),"padding"!==c&&(g+=n.css(a,"border"+R[f]+"Width",!0,e)));return g}function Ia(a,b,c){var d=!0,e="width"===b?a.offsetWidth:a.offsetHeight,f=wa(a),g="border-box"===n.css(a,"boxSizing",!1,f);if(0>=e||null==e){if(e=xa(a,b,f),(0>e||null==e)&&(e=a.style[b]),va.test(e))return e;d=g&&(k.boxSizingReliable()||e===a.style[b]),e=parseFloat(e)||0}return e+Ha(a,b,c||(g?"border":"content"),d,f)+"px"}function Ja(a,b){for(var c,d,e,f=[],g=0,h=a.length;h>g;g++)d=a[g],d.style&&(f[g]=L.get(d,"olddisplay"),c=d.style.display,b?(f[g]||"none"!==c||(d.style.display=""),""===d.style.display&&S(d)&&(f[g]=L.access(d,"olddisplay",ta(d.nodeName)))):(e=S(d),"none"===c&&e||L.set(d,"olddisplay",e?c:n.css(d,"display"))));for(g=0;h>g;g++)d=a[g],d.style&&(b&&"none"!==d.style.display&&""!==d.style.display||(d.style.display=b?f[g]||"":"none"));return a}n.extend({cssHooks:{opacity:{get:function(a,b){if(b){var c=xa(a,"opacity");return""===c?"1":c}}}},cssNumber:{columnCount:!0,fillOpacity:!0,flexGrow:!0,flexShrink:!0,fontWeight:!0,lineHeight:!0,opacity:!0,order:!0,orphans:!0,widows:!0,zIndex:!0,zoom:!0},cssProps:{"float":"cssFloat"},style:function(a,b,c,d){if(a&&3!==a.nodeType&&8!==a.nodeType&&a.style){var e,f,g,h=n.camelCase(b),i=a.style;return b=n.cssProps[h]||(n.cssProps[h]=Fa(i,h)),g=n.cssHooks[b]||n.cssHooks[h],void 0===c?g&&"get"in g&&void 0!==(e=g.get(a,!1,d))?e:i[b]:(f=typeof c,"string"===f&&(e=Ba.exec(c))&&(c=(e[1]+1)*e[2]+parseFloat(n.css(a,b)),f="number"),null!=c&&c===c&&("number"!==f||n.cssNumber[h]||(c+="px"),k.clearCloneStyle||""!==c||0!==b.indexOf("background")||(i[b]="inherit"),g&&"set"in g&&void 0===(c=g.set(a,c,d))||(i[b]=c)),void 0)}},css:function(a,b,c,d){var e,f,g,h=n.camelCase(b);return b=n.cssProps[h]||(n.cssProps[h]=Fa(a.style,h)),g=n.cssHooks[b]||n.cssHooks[h],g&&"get"in g&&(e=g.get(a,!0,c)),void 0===e&&(e=xa(a,b,d)),"normal"===e&&b in Da&&(e=Da[b]),""===c||c?(f=parseFloat(e),c===!0||n.isNumeric(f)?f||0:e):e}}),n.each(["height","width"],function(a,b){n.cssHooks[b]={get:function(a,c,d){return c?za.test(n.css(a,"display"))&&0===a.offsetWidth?n.swap(a,Ca,function(){return Ia(a,b,d)}):Ia(a,b,d):void 0},set:function(a,c,d){var e=d&&wa(a);return Ga(a,c,d?Ha(a,b,d,"border-box"===n.css(a,"boxSizing",!1,e),e):0)}}}),n.cssHooks.marginRight=ya(k.reliableMarginRight,function(a,b){return b?n.swap(a,{display:"inline-block"},xa,[a,"marginRight"]):void 0}),n.each({margin:"",padding:"",border:"Width"},function(a,b){n.cssHooks[a+b]={expand:function(c){for(var d=0,e={},f="string"==typeof c?c.split(" "):[c];4>d;d++)e[a+R[d]+b]=f[d]||f[d-2]||f[0];return e}},ua.test(a)||(n.cssHooks[a+b].set=Ga)}),n.fn.extend({css:function(a,b){return J(this,function(a,b,c){var d,e,f={},g=0;if(n.isArray(b)){for(d=wa(a),e=b.length;e>g;g++)f[b[g]]=n.css(a,b[g],!1,d);return f}return void 0!==c?n.style(a,b,c):n.css(a,b)},a,b,arguments.length>1)},show:function(){return Ja(this,!0)},hide:function(){return Ja(this)},toggle:function(a){return"boolean"==typeof a?a?this.show():this.hide():this.each(function(){S(this)?n(this).show():n(this).hide()})}});function Ka(a,b,c,d,e){return new Ka.prototype.init(a,b,c,d,e)}n.Tween=Ka,Ka.prototype={constructor:Ka,init:function(a,b,c,d,e,f){this.elem=a,this.prop=c,this.easing=e||"swing",this.options=b,this.start=this.now=this.cur(),this.end=d,this.unit=f||(n.cssNumber[c]?"":"px")},cur:function(){var a=Ka.propHooks[this.prop];return a&&a.get?a.get(this):Ka.propHooks._default.get(this)},run:function(a){var b,c=Ka.propHooks[this.prop];return this.options.duration?this.pos=b=n.easing[this.easing](a,this.options.duration*a,0,1,this.options.duration):this.pos=b=a,this.now=(this.end-this.start)*b+this.start,this.options.step&&this.options.step.call(this.elem,this.now,this),c&&c.set?c.set(this):Ka.propHooks._default.set(this),this}},Ka.prototype.init.prototype=Ka.prototype,Ka.propHooks={_default:{get:function(a){var b;return null==a.elem[a.prop]||a.elem.style&&null!=a.elem.style[a.prop]?(b=n.css(a.elem,a.prop,""),b&&"auto"!==b?b:0):a.elem[a.prop]},set:function(a){n.fx.step[a.prop]?n.fx.step[a.prop](a):a.elem.style&&(null!=a.elem.style[n.cssProps[a.prop]]||n.cssHooks[a.prop])?n.style(a.elem,a.prop,a.now+a.unit):a.elem[a.prop]=a.now}}},Ka.propHooks.scrollTop=Ka.propHooks.scrollLeft={set:function(a){a.elem.nodeType&&a.elem.parentNode&&(a.elem[a.prop]=a.now)}},n.easing={linear:function(a){return a},swing:function(a){return.5-Math.cos(a*Math.PI)/2}},n.fx=Ka.prototype.init,n.fx.step={};var La,Ma,Na=/^(?:toggle|show|hide)$/,Oa=new RegExp("^(?:([+-])=|)("+Q+")([a-z%]*)$","i"),Pa=/queueHooks$/,Qa=[Va],Ra={"*":[function(a,b){var c=this.createTween(a,b),d=c.cur(),e=Oa.exec(b),f=e&&e[3]||(n.cssNumber[a]?"":"px"),g=(n.cssNumber[a]||"px"!==f&&+d)&&Oa.exec(n.css(c.elem,a)),h=1,i=20;if(g&&g[3]!==f){f=f||g[3],e=e||[],g=+d||1;do h=h||".5",g/=h,n.style(c.elem,a,g+f);while(h!==(h=c.cur()/d)&&1!==h&&--i)}return e&&(g=c.start=+g||+d||0,c.unit=f,c.end=e[1]?g+(e[1]+1)*e[2]:+e[2]),c}]};function Sa(){return setTimeout(function(){La=void 0}),La=n.now()}function Ta(a,b){var c,d=0,e={height:a};for(b=b?1:0;4>d;d+=2-b)c=R[d],e["margin"+c]=e["padding"+c]=a;return b&&(e.opacity=e.width=a),e}function Ua(a,b,c){for(var d,e=(Ra[b]||[]).concat(Ra["*"]),f=0,g=e.length;g>f;f++)if(d=e[f].call(c,b,a))return d}function Va(a,b,c){var d,e,f,g,h,i,j,k,l=this,m={},o=a.style,p=a.nodeType&&S(a),q=L.get(a,"fxshow");c.queue||(h=n._queueHooks(a,"fx"),null==h.unqueued&&(h.unqueued=0,i=h.empty.fire,h.empty.fire=function(){h.unqueued||i()}),h.unqueued++,l.always(function(){l.always(function(){h.unqueued--,n.queue(a,"fx").length||h.empty.fire()})})),1===a.nodeType&&("height"in b||"width"in b)&&(c.overflow=[o.overflow,o.overflowX,o.overflowY],j=n.css(a,"display"),k="none"===j?L.get(a,"olddisplay")||ta(a.nodeName):j,"inline"===k&&"none"===n.css(a,"float")&&(o.display="inline-block")),c.overflow&&(o.overflow="hidden",l.always(function(){o.overflow=c.overflow[0],o.overflowX=c.overflow[1],o.overflowY=c.overflow[2]}));for(d in b)if(e=b[d],Na.exec(e)){if(delete b[d],f=f||"toggle"===e,e===(p?"hide":"show")){if("show"!==e||!q||void 0===q[d])continue;p=!0}m[d]=q&&q[d]||n.style(a,d)}else j=void 0;if(n.isEmptyObject(m))"inline"===("none"===j?ta(a.nodeName):j)&&(o.display=j);else{q?"hidden"in q&&(p=q.hidden):q=L.access(a,"fxshow",{}),f&&(q.hidden=!p),p?n(a).show():l.done(function(){n(a).hide()}),l.done(function(){var b;L.remove(a,"fxshow");for(b in m)n.style(a,b,m[b])});for(d in m)g=Ua(p?q[d]:0,d,l),d in q||(q[d]=g.start,p&&(g.end=g.start,g.start="width"===d||"height"===d?1:0))}}function Wa(a,b){var c,d,e,f,g;for(c in a)if(d=n.camelCase(c),e=b[d],f=a[c],n.isArray(f)&&(e=f[1],f=a[c]=f[0]),c!==d&&(a[d]=f,delete a[c]),g=n.cssHooks[d],g&&"expand"in g){f=g.expand(f),delete a[d];for(c in f)c in a||(a[c]=f[c],b[c]=e)}else b[d]=e}function Xa(a,b,c){var d,e,f=0,g=Qa.length,h=n.Deferred().always(function(){delete i.elem}),i=function(){if(e)return!1;for(var b=La||Sa(),c=Math.max(0,j.startTime+j.duration-b),d=c/j.duration||0,f=1-d,g=0,i=j.tweens.length;i>g;g++)j.tweens[g].run(f);return h.notifyWith(a,[j,f,c]),1>f&&i?c:(h.resolveWith(a,[j]),!1)},j=h.promise({elem:a,props:n.extend({},b),opts:n.extend(!0,{specialEasing:{}},c),originalProperties:b,originalOptions:c,startTime:La||Sa(),duration:c.duration,tweens:[],createTween:function(b,c){var d=n.Tween(a,j.opts,b,c,j.opts.specialEasing[b]||j.opts.easing);return j.tweens.push(d),d},stop:function(b){var c=0,d=b?j.tweens.length:0;if(e)return this;for(e=!0;d>c;c++)j.tweens[c].run(1);return b?h.resolveWith(a,[j,b]):h.rejectWith(a,[j,b]),this}}),k=j.props;for(Wa(k,j.opts.specialEasing);g>f;f++)if(d=Qa[f].call(j,a,k,j.opts))return d;return n.map(k,Ua,j),n.isFunction(j.opts.start)&&j.opts.start.call(a,j),n.fx.timer(n.extend(i,{elem:a,anim:j,queue:j.opts.queue})),j.progress(j.opts.progress).done(j.opts.done,j.opts.complete).fail(j.opts.fail).always(j.opts.always)}n.Animation=n.extend(Xa,{tweener:function(a,b){n.isFunction(a)?(b=a,a=["*"]):a=a.split(" ");for(var c,d=0,e=a.length;e>d;d++)c=a[d],Ra[c]=Ra[c]||[],Ra[c].unshift(b)},prefilter:function(a,b){b?Qa.unshift(a):Qa.push(a)}}),n.speed=function(a,b,c){var d=a&&"object"==typeof a?n.extend({},a):{complete:c||!c&&b||n.isFunction(a)&&a,duration:a,easing:c&&b||b&&!n.isFunction(b)&&b};return d.duration=n.fx.off?0:"number"==typeof d.duration?d.duration:d.duration in n.fx.speeds?n.fx.speeds[d.duration]:n.fx.speeds._default,(null==d.queue||d.queue===!0)&&(d.queue="fx"),d.old=d.complete,d.complete=function(){n.isFunction(d.old)&&d.old.call(this),d.queue&&n.dequeue(this,d.queue)},d},n.fn.extend({fadeTo:function(a,b,c,d){return this.filter(S).css("opacity",0).show().end().animate({opacity:b},a,c,d)},animate:function(a,b,c,d){var e=n.isEmptyObject(a),f=n.speed(b,c,d),g=function(){var b=Xa(this,n.extend({},a),f);(e||L.get(this,"finish"))&&b.stop(!0)};return g.finish=g,e||f.queue===!1?this.each(g):this.queue(f.queue,g)},stop:function(a,b,c){var d=function(a){var b=a.stop;delete a.stop,b(c)};return"string"!=typeof a&&(c=b,b=a,a=void 0),b&&a!==!1&&this.queue(a||"fx",[]),this.each(function(){var b=!0,e=null!=a&&a+"queueHooks",f=n.timers,g=L.get(this);if(e)g[e]&&g[e].stop&&d(g[e]);else for(e in g)g[e]&&g[e].stop&&Pa.test(e)&&d(g[e]);for(e=f.length;e--;)f[e].elem!==this||null!=a&&f[e].queue!==a||(f[e].anim.stop(c),b=!1,f.splice(e,1));(b||!c)&&n.dequeue(this,a)})},finish:function(a){return a!==!1&&(a=a||"fx"),this.each(function(){var b,c=L.get(this),d=c[a+"queue"],e=c[a+"queueHooks"],f=n.timers,g=d?d.length:0;for(c.finish=!0,n.queue(this,a,[]),e&&e.stop&&e.stop.call(this,!0),b=f.length;b--;)f[b].elem===this&&f[b].queue===a&&(f[b].anim.stop(!0),f.splice(b,1));for(b=0;g>b;b++)d[b]&&d[b].finish&&d[b].finish.call(this);delete c.finish})}}),n.each(["toggle","show","hide"],function(a,b){var c=n.fn[b];n.fn[b]=function(a,d,e){return null==a||"boolean"==typeof a?c.apply(this,arguments):this.animate(Ta(b,!0),a,d,e)}}),n.each({slideDown:Ta("show"),slideUp:Ta("hide"),slideToggle:Ta("toggle"),fadeIn:{opacity:"show"},fadeOut:{opacity:"hide"},fadeToggle:{opacity:"toggle"}},function(a,b){n.fn[a]=function(a,c,d){return this.animate(b,a,c,d)}}),n.timers=[],n.fx.tick=function(){var a,b=0,c=n.timers;for(La=n.now();b<c.length;b++)a=c[b],a()||c[b]!==a||c.splice(b--,1);c.length||n.fx.stop(),La=void 0},n.fx.timer=function(a){n.timers.push(a),a()?n.fx.start():n.timers.pop()},n.fx.interval=13,n.fx.start=function(){Ma||(Ma=setInterval(n.fx.tick,n.fx.interval))},n.fx.stop=function(){clearInterval(Ma),Ma=null},n.fx.speeds={slow:600,fast:200,_default:400},n.fn.delay=function(a,b){return a=n.fx?n.fx.speeds[a]||a:a,b=b||"fx",this.queue(b,function(b,c){var d=setTimeout(b,a);c.stop=function(){clearTimeout(d)}})},function(){var a=l.createElement("input"),b=l.createElement("select"),c=b.appendChild(l.createElement("option"));a.type="checkbox",k.checkOn=""!==a.value,k.optSelected=c.selected,b.disabled=!0,k.optDisabled=!c.disabled,a=l.createElement("input"),a.value="t",a.type="radio",k.radioValue="t"===a.value}();var Ya,Za,$a=n.expr.attrHandle;n.fn.extend({attr:function(a,b){return J(this,n.attr,a,b,arguments.length>1)},removeAttr:function(a){return this.each(function(){n.removeAttr(this,a)})}}),n.extend({attr:function(a,b,c){var d,e,f=a.nodeType;if(a&&3!==f&&8!==f&&2!==f)return typeof a.getAttribute===U?n.prop(a,b,c):(1===f&&n.isXMLDoc(a)||(b=b.toLowerCase(),d=n.attrHooks[b]||(n.expr.match.bool.test(b)?Za:Ya)),
void 0===c?d&&"get"in d&&null!==(e=d.get(a,b))?e:(e=n.find.attr(a,b),null==e?void 0:e):null!==c?d&&"set"in d&&void 0!==(e=d.set(a,c,b))?e:(a.setAttribute(b,c+""),c):void n.removeAttr(a,b))},removeAttr:function(a,b){var c,d,e=0,f=b&&b.match(E);if(f&&1===a.nodeType)while(c=f[e++])d=n.propFix[c]||c,n.expr.match.bool.test(c)&&(a[d]=!1),a.removeAttribute(c)},attrHooks:{type:{set:function(a,b){if(!k.radioValue&&"radio"===b&&n.nodeName(a,"input")){var c=a.value;return a.setAttribute("type",b),c&&(a.value=c),b}}}}}),Za={set:function(a,b,c){return b===!1?n.removeAttr(a,c):a.setAttribute(c,c),c}},n.each(n.expr.match.bool.source.match(/\w+/g),function(a,b){var c=$a[b]||n.find.attr;$a[b]=function(a,b,d){var e,f;return d||(f=$a[b],$a[b]=e,e=null!=c(a,b,d)?b.toLowerCase():null,$a[b]=f),e}});var _a=/^(?:input|select|textarea|button)$/i;n.fn.extend({prop:function(a,b){return J(this,n.prop,a,b,arguments.length>1)},removeProp:function(a){return this.each(function(){delete this[n.propFix[a]||a]})}}),n.extend({propFix:{"for":"htmlFor","class":"className"},prop:function(a,b,c){var d,e,f,g=a.nodeType;if(a&&3!==g&&8!==g&&2!==g)return f=1!==g||!n.isXMLDoc(a),f&&(b=n.propFix[b]||b,e=n.propHooks[b]),void 0!==c?e&&"set"in e&&void 0!==(d=e.set(a,c,b))?d:a[b]=c:e&&"get"in e&&null!==(d=e.get(a,b))?d:a[b]},propHooks:{tabIndex:{get:function(a){return a.hasAttribute("tabindex")||_a.test(a.nodeName)||a.href?a.tabIndex:-1}}}}),k.optSelected||(n.propHooks.selected={get:function(a){var b=a.parentNode;return b&&b.parentNode&&b.parentNode.selectedIndex,null}}),n.each(["tabIndex","readOnly","maxLength","cellSpacing","cellPadding","rowSpan","colSpan","useMap","frameBorder","contentEditable"],function(){n.propFix[this.toLowerCase()]=this});var ab=/[\t\r\n\f]/g;n.fn.extend({addClass:function(a){var b,c,d,e,f,g,h="string"==typeof a&&a,i=0,j=this.length;if(n.isFunction(a))return this.each(function(b){n(this).addClass(a.call(this,b,this.className))});if(h)for(b=(a||"").match(E)||[];j>i;i++)if(c=this[i],d=1===c.nodeType&&(c.className?(" "+c.className+" ").replace(ab," "):" ")){f=0;while(e=b[f++])d.indexOf(" "+e+" ")<0&&(d+=e+" ");g=n.trim(d),c.className!==g&&(c.className=g)}return this},removeClass:function(a){var b,c,d,e,f,g,h=0===arguments.length||"string"==typeof a&&a,i=0,j=this.length;if(n.isFunction(a))return this.each(function(b){n(this).removeClass(a.call(this,b,this.className))});if(h)for(b=(a||"").match(E)||[];j>i;i++)if(c=this[i],d=1===c.nodeType&&(c.className?(" "+c.className+" ").replace(ab," "):"")){f=0;while(e=b[f++])while(d.indexOf(" "+e+" ")>=0)d=d.replace(" "+e+" "," ");g=a?n.trim(d):"",c.className!==g&&(c.className=g)}return this},toggleClass:function(a,b){var c=typeof a;return"boolean"==typeof b&&"string"===c?b?this.addClass(a):this.removeClass(a):this.each(n.isFunction(a)?function(c){n(this).toggleClass(a.call(this,c,this.className,b),b)}:function(){if("string"===c){var b,d=0,e=n(this),f=a.match(E)||[];while(b=f[d++])e.hasClass(b)?e.removeClass(b):e.addClass(b)}else(c===U||"boolean"===c)&&(this.className&&L.set(this,"__className__",this.className),this.className=this.className||a===!1?"":L.get(this,"__className__")||"")})},hasClass:function(a){for(var b=" "+a+" ",c=0,d=this.length;d>c;c++)if(1===this[c].nodeType&&(" "+this[c].className+" ").replace(ab," ").indexOf(b)>=0)return!0;return!1}});var bb=/\r/g;n.fn.extend({val:function(a){var b,c,d,e=this[0];{if(arguments.length)return d=n.isFunction(a),this.each(function(c){var e;1===this.nodeType&&(e=d?a.call(this,c,n(this).val()):a,null==e?e="":"number"==typeof e?e+="":n.isArray(e)&&(e=n.map(e,function(a){return null==a?"":a+""})),b=n.valHooks[this.type]||n.valHooks[this.nodeName.toLowerCase()],b&&"set"in b&&void 0!==b.set(this,e,"value")||(this.value=e))});if(e)return b=n.valHooks[e.type]||n.valHooks[e.nodeName.toLowerCase()],b&&"get"in b&&void 0!==(c=b.get(e,"value"))?c:(c=e.value,"string"==typeof c?c.replace(bb,""):null==c?"":c)}}}),n.extend({valHooks:{option:{get:function(a){var b=n.find.attr(a,"value");return null!=b?b:n.trim(n.text(a))}},select:{get:function(a){for(var b,c,d=a.options,e=a.selectedIndex,f="select-one"===a.type||0>e,g=f?null:[],h=f?e+1:d.length,i=0>e?h:f?e:0;h>i;i++)if(c=d[i],!(!c.selected&&i!==e||(k.optDisabled?c.disabled:null!==c.getAttribute("disabled"))||c.parentNode.disabled&&n.nodeName(c.parentNode,"optgroup"))){if(b=n(c).val(),f)return b;g.push(b)}return g},set:function(a,b){var c,d,e=a.options,f=n.makeArray(b),g=e.length;while(g--)d=e[g],(d.selected=n.inArray(d.value,f)>=0)&&(c=!0);return c||(a.selectedIndex=-1),f}}}}),n.each(["radio","checkbox"],function(){n.valHooks[this]={set:function(a,b){return n.isArray(b)?a.checked=n.inArray(n(a).val(),b)>=0:void 0}},k.checkOn||(n.valHooks[this].get=function(a){return null===a.getAttribute("value")?"on":a.value})}),n.each("blur focus focusin focusout load resize scroll unload click dblclick mousedown mouseup mousemove mouseover mouseout mouseenter mouseleave change select submit keydown keypress keyup error contextmenu".split(" "),function(a,b){n.fn[b]=function(a,c){return arguments.length>0?this.on(b,null,a,c):this.trigger(b)}}),n.fn.extend({hover:function(a,b){return this.mouseenter(a).mouseleave(b||a)},bind:function(a,b,c){return this.on(a,null,b,c)},unbind:function(a,b){return this.off(a,null,b)},delegate:function(a,b,c,d){return this.on(b,a,c,d)},undelegate:function(a,b,c){return 1===arguments.length?this.off(a,"**"):this.off(b,a||"**",c)}});var cb=n.now(),db=/\?/;n.parseJSON=function(a){return JSON.parse(a+"")},n.parseXML=function(a){var b,c;if(!a||"string"!=typeof a)return null;try{c=new DOMParser,b=c.parseFromString(a,"text/xml")}catch(d){b=void 0}return(!b||b.getElementsByTagName("parsererror").length)&&n.error("Invalid XML: "+a),b};var eb=/#.*$/,fb=/([?&])_=[^&]*/,gb=/^(.*?):[ \t]*([^\r\n]*)$/gm,hb=/^(?:about|app|app-storage|.+-extension|file|res|widget):$/,ib=/^(?:GET|HEAD)$/,jb=/^\/\//,kb=/^([\w.+-]+:)(?:\/\/(?:[^\/?#]*@|)([^\/?#:]*)(?::(\d+)|)|)/,lb={},mb={},nb="*/".concat("*"),ob=a.location.href,pb=kb.exec(ob.toLowerCase())||[];function qb(a){return function(b,c){"string"!=typeof b&&(c=b,b="*");var d,e=0,f=b.toLowerCase().match(E)||[];if(n.isFunction(c))while(d=f[e++])"+"===d[0]?(d=d.slice(1)||"*",(a[d]=a[d]||[]).unshift(c)):(a[d]=a[d]||[]).push(c)}}function rb(a,b,c,d){var e={},f=a===mb;function g(h){var i;return e[h]=!0,n.each(a[h]||[],function(a,h){var j=h(b,c,d);return"string"!=typeof j||f||e[j]?f?!(i=j):void 0:(b.dataTypes.unshift(j),g(j),!1)}),i}return g(b.dataTypes[0])||!e["*"]&&g("*")}function sb(a,b){var c,d,e=n.ajaxSettings.flatOptions||{};for(c in b)void 0!==b[c]&&((e[c]?a:d||(d={}))[c]=b[c]);return d&&n.extend(!0,a,d),a}function tb(a,b,c){var d,e,f,g,h=a.contents,i=a.dataTypes;while("*"===i[0])i.shift(),void 0===d&&(d=a.mimeType||b.getResponseHeader("Content-Type"));if(d)for(e in h)if(h[e]&&h[e].test(d)){i.unshift(e);break}if(i[0]in c)f=i[0];else{for(e in c){if(!i[0]||a.converters[e+" "+i[0]]){f=e;break}g||(g=e)}f=f||g}return f?(f!==i[0]&&i.unshift(f),c[f]):void 0}function ub(a,b,c,d){var e,f,g,h,i,j={},k=a.dataTypes.slice();if(k[1])for(g in a.converters)j[g.toLowerCase()]=a.converters[g];f=k.shift();while(f)if(a.responseFields[f]&&(c[a.responseFields[f]]=b),!i&&d&&a.dataFilter&&(b=a.dataFilter(b,a.dataType)),i=f,f=k.shift())if("*"===f)f=i;else if("*"!==i&&i!==f){if(g=j[i+" "+f]||j["* "+f],!g)for(e in j)if(h=e.split(" "),h[1]===f&&(g=j[i+" "+h[0]]||j["* "+h[0]])){g===!0?g=j[e]:j[e]!==!0&&(f=h[0],k.unshift(h[1]));break}if(g!==!0)if(g&&a["throws"])b=g(b);else try{b=g(b)}catch(l){return{state:"parsererror",error:g?l:"No conversion from "+i+" to "+f}}}return{state:"success",data:b}}n.extend({active:0,lastModified:{},etag:{},ajaxSettings:{url:ob,type:"GET",isLocal:hb.test(pb[1]),global:!0,processData:!0,async:!0,contentType:"application/x-www-form-urlencoded; charset=UTF-8",accepts:{"*":nb,text:"text/plain",html:"text/html",xml:"application/xml, text/xml",json:"application/json, text/javascript"},contents:{xml:/xml/,html:/html/,json:/json/},responseFields:{xml:"responseXML",text:"responseText",json:"responseJSON"},converters:{"* text":String,"text html":!0,"text json":n.parseJSON,"text xml":n.parseXML},flatOptions:{url:!0,context:!0}},ajaxSetup:function(a,b){return b?sb(sb(a,n.ajaxSettings),b):sb(n.ajaxSettings,a)},ajaxPrefilter:qb(lb),ajaxTransport:qb(mb),ajax:function(a,b){"object"==typeof a&&(b=a,a=void 0),b=b||{};var c,d,e,f,g,h,i,j,k=n.ajaxSetup({},b),l=k.context||k,m=k.context&&(l.nodeType||l.jquery)?n(l):n.event,o=n.Deferred(),p=n.Callbacks("once memory"),q=k.statusCode||{},r={},s={},t=0,u="canceled",v={readyState:0,getResponseHeader:function(a){var b;if(2===t){if(!f){f={};while(b=gb.exec(e))f[b[1].toLowerCase()]=b[2]}b=f[a.toLowerCase()]}return null==b?null:b},getAllResponseHeaders:function(){return 2===t?e:null},setRequestHeader:function(a,b){var c=a.toLowerCase();return t||(a=s[c]=s[c]||a,r[a]=b),this},overrideMimeType:function(a){return t||(k.mimeType=a),this},statusCode:function(a){var b;if(a)if(2>t)for(b in a)q[b]=[q[b],a[b]];else v.always(a[v.status]);return this},abort:function(a){var b=a||u;return c&&c.abort(b),x(0,b),this}};if(o.promise(v).complete=p.add,v.success=v.done,v.error=v.fail,k.url=((a||k.url||ob)+"").replace(eb,"").replace(jb,pb[1]+"//"),k.type=b.method||b.type||k.method||k.type,k.dataTypes=n.trim(k.dataType||"*").toLowerCase().match(E)||[""],null==k.crossDomain&&(h=kb.exec(k.url.toLowerCase()),k.crossDomain=!(!h||h[1]===pb[1]&&h[2]===pb[2]&&(h[3]||("http:"===h[1]?"80":"443"))===(pb[3]||("http:"===pb[1]?"80":"443")))),k.data&&k.processData&&"string"!=typeof k.data&&(k.data=n.param(k.data,k.traditional)),rb(lb,k,b,v),2===t)return v;i=n.event&&k.global,i&&0===n.active++&&n.event.trigger("ajaxStart"),k.type=k.type.toUpperCase(),k.hasContent=!ib.test(k.type),d=k.url,k.hasContent||(k.data&&(d=k.url+=(db.test(d)?"&":"?")+k.data,delete k.data),k.cache===!1&&(k.url=fb.test(d)?d.replace(fb,"$1_="+cb++):d+(db.test(d)?"&":"?")+"_="+cb++)),k.ifModified&&(n.lastModified[d]&&v.setRequestHeader("If-Modified-Since",n.lastModified[d]),n.etag[d]&&v.setRequestHeader("If-None-Match",n.etag[d])),(k.data&&k.hasContent&&k.contentType!==!1||b.contentType)&&v.setRequestHeader("Content-Type",k.contentType),v.setRequestHeader("Accept",k.dataTypes[0]&&k.accepts[k.dataTypes[0]]?k.accepts[k.dataTypes[0]]+("*"!==k.dataTypes[0]?", "+nb+"; q=0.01":""):k.accepts["*"]);for(j in k.headers)v.setRequestHeader(j,k.headers[j]);if(k.beforeSend&&(k.beforeSend.call(l,v,k)===!1||2===t))return v.abort();u="abort";for(j in{success:1,error:1,complete:1})v[j](k[j]);if(c=rb(mb,k,b,v)){v.readyState=1,i&&m.trigger("ajaxSend",[v,k]),k.async&&k.timeout>0&&(g=setTimeout(function(){v.abort("timeout")},k.timeout));try{t=1,c.send(r,x)}catch(w){if(!(2>t))throw w;x(-1,w)}}else x(-1,"No Transport");function x(a,b,f,h){var j,r,s,u,w,x=b;2!==t&&(t=2,g&&clearTimeout(g),c=void 0,e=h||"",v.readyState=a>0?4:0,j=a>=200&&300>a||304===a,f&&(u=tb(k,v,f)),u=ub(k,u,v,j),j?(k.ifModified&&(w=v.getResponseHeader("Last-Modified"),w&&(n.lastModified[d]=w),w=v.getResponseHeader("etag"),w&&(n.etag[d]=w)),204===a||"HEAD"===k.type?x="nocontent":304===a?x="notmodified":(x=u.state,r=u.data,s=u.error,j=!s)):(s=x,(a||!x)&&(x="error",0>a&&(a=0))),v.status=a,v.statusText=(b||x)+"",j?o.resolveWith(l,[r,x,v]):o.rejectWith(l,[v,x,s]),v.statusCode(q),q=void 0,i&&m.trigger(j?"ajaxSuccess":"ajaxError",[v,k,j?r:s]),p.fireWith(l,[v,x]),i&&(m.trigger("ajaxComplete",[v,k]),--n.active||n.event.trigger("ajaxStop")))}return v},getJSON:function(a,b,c){return n.get(a,b,c,"json")},getScript:function(a,b){return n.get(a,void 0,b,"script")}}),n.each(["get","post"],function(a,b){n[b]=function(a,c,d,e){return n.isFunction(c)&&(e=e||d,d=c,c=void 0),n.ajax({url:a,type:b,dataType:e,data:c,success:d})}}),n._evalUrl=function(a){return n.ajax({url:a,type:"GET",dataType:"script",async:!1,global:!1,"throws":!0})},n.fn.extend({wrapAll:function(a){var b;return n.isFunction(a)?this.each(function(b){n(this).wrapAll(a.call(this,b))}):(this[0]&&(b=n(a,this[0].ownerDocument).eq(0).clone(!0),this[0].parentNode&&b.insertBefore(this[0]),b.map(function(){var a=this;while(a.firstElementChild)a=a.firstElementChild;return a}).append(this)),this)},wrapInner:function(a){return this.each(n.isFunction(a)?function(b){n(this).wrapInner(a.call(this,b))}:function(){var b=n(this),c=b.contents();c.length?c.wrapAll(a):b.append(a)})},wrap:function(a){var b=n.isFunction(a);return this.each(function(c){n(this).wrapAll(b?a.call(this,c):a)})},unwrap:function(){return this.parent().each(function(){n.nodeName(this,"body")||n(this).replaceWith(this.childNodes)}).end()}}),n.expr.filters.hidden=function(a){return a.offsetWidth<=0&&a.offsetHeight<=0},n.expr.filters.visible=function(a){return!n.expr.filters.hidden(a)};var vb=/%20/g,wb=/\[\]$/,xb=/\r?\n/g,yb=/^(?:submit|button|image|reset|file)$/i,zb=/^(?:input|select|textarea|keygen)/i;function Ab(a,b,c,d){var e;if(n.isArray(b))n.each(b,function(b,e){c||wb.test(a)?d(a,e):Ab(a+"["+("object"==typeof e?b:"")+"]",e,c,d)});else if(c||"object"!==n.type(b))d(a,b);else for(e in b)Ab(a+"["+e+"]",b[e],c,d)}n.param=function(a,b){var c,d=[],e=function(a,b){b=n.isFunction(b)?b():null==b?"":b,d[d.length]=encodeURIComponent(a)+"="+encodeURIComponent(b)};if(void 0===b&&(b=n.ajaxSettings&&n.ajaxSettings.traditional),n.isArray(a)||a.jquery&&!n.isPlainObject(a))n.each(a,function(){e(this.name,this.value)});else for(c in a)Ab(c,a[c],b,e);return d.join("&").replace(vb,"+")},n.fn.extend({serialize:function(){return n.param(this.serializeArray())},serializeArray:function(){return this.map(function(){var a=n.prop(this,"elements");return a?n.makeArray(a):this}).filter(function(){var a=this.type;return this.name&&!n(this).is(":disabled")&&zb.test(this.nodeName)&&!yb.test(a)&&(this.checked||!T.test(a))}).map(function(a,b){var c=n(this).val();return null==c?null:n.isArray(c)?n.map(c,function(a){return{name:b.name,value:a.replace(xb,"\r\n")}}):{name:b.name,value:c.replace(xb,"\r\n")}}).get()}}),n.ajaxSettings.xhr=function(){try{return new XMLHttpRequest}catch(a){}};var Bb=0,Cb={},Db={0:200,1223:204},Eb=n.ajaxSettings.xhr();a.attachEvent&&a.attachEvent("onunload",function(){for(var a in Cb)Cb[a]()}),k.cors=!!Eb&&"withCredentials"in Eb,k.ajax=Eb=!!Eb,n.ajaxTransport(function(a){var b;return k.cors||Eb&&!a.crossDomain?{send:function(c,d){var e,f=a.xhr(),g=++Bb;if(f.open(a.type,a.url,a.async,a.username,a.password),a.xhrFields)for(e in a.xhrFields)f[e]=a.xhrFields[e];a.mimeType&&f.overrideMimeType&&f.overrideMimeType(a.mimeType),a.crossDomain||c["X-Requested-With"]||(c["X-Requested-With"]="XMLHttpRequest");for(e in c)f.setRequestHeader(e,c[e]);b=function(a){return function(){b&&(delete Cb[g],b=f.onload=f.onerror=null,"abort"===a?f.abort():"error"===a?d(f.status,f.statusText):d(Db[f.status]||f.status,f.statusText,"string"==typeof f.responseText?{text:f.responseText}:void 0,f.getAllResponseHeaders()))}},f.onload=b(),f.onerror=b("error"),b=Cb[g]=b("abort");try{f.send(a.hasContent&&a.data||null)}catch(h){if(b)throw h}},abort:function(){b&&b()}}:void 0}),n.ajaxSetup({accepts:{script:"text/javascript, application/javascript, application/ecmascript, application/x-ecmascript"},contents:{script:/(?:java|ecma)script/},converters:{"text script":function(a){return n.globalEval(a),a}}}),n.ajaxPrefilter("script",function(a){void 0===a.cache&&(a.cache=!1),a.crossDomain&&(a.type="GET")}),n.ajaxTransport("script",function(a){if(a.crossDomain){var b,c;return{send:function(d,e){b=n("<script>").prop({async:!0,charset:a.scriptCharset,src:a.url}).on("load error",c=function(a){b.remove(),c=null,a&&e("error"===a.type?404:200,a.type)}),l.head.appendChild(b[0])},abort:function(){c&&c()}}}});var Fb=[],Gb=/(=)\?(?=&|$)|\?\?/;n.ajaxSetup({jsonp:"callback",jsonpCallback:function(){var a=Fb.pop()||n.expando+"_"+cb++;return this[a]=!0,a}}),n.ajaxPrefilter("json jsonp",function(b,c,d){var e,f,g,h=b.jsonp!==!1&&(Gb.test(b.url)?"url":"string"==typeof b.data&&!(b.contentType||"").indexOf("application/x-www-form-urlencoded")&&Gb.test(b.data)&&"data");return h||"jsonp"===b.dataTypes[0]?(e=b.jsonpCallback=n.isFunction(b.jsonpCallback)?b.jsonpCallback():b.jsonpCallback,h?b[h]=b[h].replace(Gb,"$1"+e):b.jsonp!==!1&&(b.url+=(db.test(b.url)?"&":"?")+b.jsonp+"="+e),b.converters["script json"]=function(){return g||n.error(e+" was not called"),g[0]},b.dataTypes[0]="json",f=a[e],a[e]=function(){g=arguments},d.always(function(){a[e]=f,b[e]&&(b.jsonpCallback=c.jsonpCallback,Fb.push(e)),g&&n.isFunction(f)&&f(g[0]),g=f=void 0}),"script"):void 0}),n.parseHTML=function(a,b,c){if(!a||"string"!=typeof a)return null;"boolean"==typeof b&&(c=b,b=!1),b=b||l;var d=v.exec(a),e=!c&&[];return d?[b.createElement(d[1])]:(d=n.buildFragment([a],b,e),e&&e.length&&n(e).remove(),n.merge([],d.childNodes))};var Hb=n.fn.load;n.fn.load=function(a,b,c){if("string"!=typeof a&&Hb)return Hb.apply(this,arguments);var d,e,f,g=this,h=a.indexOf(" ");return h>=0&&(d=n.trim(a.slice(h)),a=a.slice(0,h)),n.isFunction(b)?(c=b,b=void 0):b&&"object"==typeof b&&(e="POST"),g.length>0&&n.ajax({url:a,type:e,dataType:"html",data:b}).done(function(a){f=arguments,g.html(d?n("<div>").append(n.parseHTML(a)).find(d):a)}).complete(c&&function(a,b){g.each(c,f||[a.responseText,b,a])}),this},n.each(["ajaxStart","ajaxStop","ajaxComplete","ajaxError","ajaxSuccess","ajaxSend"],function(a,b){n.fn[b]=function(a){return this.on(b,a)}}),n.expr.filters.animated=function(a){return n.grep(n.timers,function(b){return a===b.elem}).length};var Ib=a.document.documentElement;function Jb(a){return n.isWindow(a)?a:9===a.nodeType&&a.defaultView}n.offset={setOffset:function(a,b,c){var d,e,f,g,h,i,j,k=n.css(a,"position"),l=n(a),m={};"static"===k&&(a.style.position="relative"),h=l.offset(),f=n.css(a,"top"),i=n.css(a,"left"),j=("absolute"===k||"fixed"===k)&&(f+i).indexOf("auto")>-1,j?(d=l.position(),g=d.top,e=d.left):(g=parseFloat(f)||0,e=parseFloat(i)||0),n.isFunction(b)&&(b=b.call(a,c,h)),null!=b.top&&(m.top=b.top-h.top+g),null!=b.left&&(m.left=b.left-h.left+e),"using"in b?b.using.call(a,m):l.css(m)}},n.fn.extend({offset:function(a){if(arguments.length)return void 0===a?this:this.each(function(b){n.offset.setOffset(this,a,b)});var b,c,d=this[0],e={top:0,left:0},f=d&&d.ownerDocument;if(f)return b=f.documentElement,n.contains(b,d)?(typeof d.getBoundingClientRect!==U&&(e=d.getBoundingClientRect()),c=Jb(f),{top:e.top+c.pageYOffset-b.clientTop,left:e.left+c.pageXOffset-b.clientLeft}):e},position:function(){if(this[0]){var a,b,c=this[0],d={top:0,left:0};return"fixed"===n.css(c,"position")?b=c.getBoundingClientRect():(a=this.offsetParent(),b=this.offset(),n.nodeName(a[0],"html")||(d=a.offset()),d.top+=n.css(a[0],"borderTopWidth",!0),d.left+=n.css(a[0],"borderLeftWidth",!0)),{top:b.top-d.top-n.css(c,"marginTop",!0),left:b.left-d.left-n.css(c,"marginLeft",!0)}}},offsetParent:function(){return this.map(function(){var a=this.offsetParent||Ib;while(a&&!n.nodeName(a,"html")&&"static"===n.css(a,"position"))a=a.offsetParent;return a||Ib})}}),n.each({scrollLeft:"pageXOffset",scrollTop:"pageYOffset"},function(b,c){var d="pageYOffset"===c;n.fn[b]=function(e){return J(this,function(b,e,f){var g=Jb(b);return void 0===f?g?g[c]:b[e]:void(g?g.scrollTo(d?a.pageXOffset:f,d?f:a.pageYOffset):b[e]=f)},b,e,arguments.length,null)}}),n.each(["top","left"],function(a,b){n.cssHooks[b]=ya(k.pixelPosition,function(a,c){return c?(c=xa(a,b),va.test(c)?n(a).position()[b]+"px":c):void 0})}),n.each({Height:"height",Width:"width"},function(a,b){n.each({padding:"inner"+a,content:b,"":"outer"+a},function(c,d){n.fn[d]=function(d,e){var f=arguments.length&&(c||"boolean"!=typeof d),g=c||(d===!0||e===!0?"margin":"border");return J(this,function(b,c,d){var e;return n.isWindow(b)?b.document.documentElement["client"+a]:9===b.nodeType?(e=b.documentElement,Math.max(b.body["scroll"+a],e["scroll"+a],b.body["offset"+a],e["offset"+a],e["client"+a])):void 0===d?n.css(b,c,g):n.style(b,c,d,g)},b,f?d:void 0,f,null)}})}),n.fn.size=function(){return this.length},n.fn.andSelf=n.fn.addBack,"function"==typeof define&&define.amd&&define("jquery",[],function(){return n});var Kb=a.jQuery,Lb=a.$;return n.noConflict=function(b){return a.$===n&&(a.$=Lb),b&&a.jQuery===n&&(a.jQuery=Kb),n},typeof b===U&&(a.jQuery=a.$=n),n});
//# sourceMappingURL=jquery.min.map
/* Copyright (C) 1991-2017 Free Software Foundation, Inc.
   This file is part of the GNU C Library.

   The GNU C Library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2.1 of the License, or (at your option) any later version.

   The GNU C Library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public
   License along with the GNU C Library; if not, see
   <http://www.gnu.org/licenses/>.  */
/* This header is separate from features.h so that the compiler can
   include it implicitly at the start of every compilation.  It must
   not itself include <features.h> or any other header that includes
   <features.h> because the implicit include comes before any feature
   test macros that may be defined in a source file before it first
   explicitly includes a system header.  GCC knows the name of this
   header in order to preinclude it.  */
/* glibc's intent is to support the IEC 559 math functionality, real
   and complex.  If the GCC (4.9 and later) predefined macros
   specifying compiler intent are available, use them to determine
   whether the overall intent is to support these features; otherwise,
   presume an older compiler has intent to support these features and
   define these macros by default.  */
/* wchar_t uses Unicode 8.0.0.  Version 8.0 of the Unicode Standard is
   synchronized with ISO/IEC 10646:2014, plus Amendment 1 (published
   2015-05-15).  */
/* We do not support C11 <threads.h>.  */
 /*
 * # Semantic UI - 2.4.1
 * https://github.com/Semantic-Org/Semantic-UI
 * http://www.semantic-ui.com/
 *
 * Copyright 2014 Contributors
 * Released under the MIT license
 * http://opensource.org/licenses/MIT
 *
 */
!function(p,h,v,b){p.site=p.fn.site=function(e){var s,l,i=(new Date).getTime(),o=[],t=e,n="string"==typeof t,c=[].slice.call(arguments,1),u=p.isPlainObject(e)?p.extend(!0,{},p.site.settings,e):p.extend({},p.site.settings),a=u.namespace,d=u.error,r="module-"+a,f=p(v),m=this,g=f.data(r);return s={initialize:function(){s.instantiate()},instantiate:function(){s.verbose("Storing instance of site",s),g=s,f.data(r,s)},normalize:function(){s.fix.console(),s.fix.requestAnimationFrame()},fix:{console:function(){s.debug("Normalizing window.console"),console!==b&&console.log!==b||(s.verbose("Console not available, normalizing events"),s.disable.console()),void 0!==console.group&&void 0!==console.groupEnd&&void 0!==console.groupCollapsed||(s.verbose("Console group not available, normalizing events"),h.console.group=function(){},h.console.groupEnd=function(){},h.console.groupCollapsed=function(){}),void 0===console.markTimeline&&(s.verbose("Mark timeline not available, normalizing events"),h.console.markTimeline=function(){})},consoleClear:function(){s.debug("Disabling programmatic console clearing"),h.console.clear=function(){}},requestAnimationFrame:function(){s.debug("Normalizing requestAnimationFrame"),h.requestAnimationFrame===b&&(s.debug("RequestAnimationFrame not available, normalizing event"),h.requestAnimationFrame=h.requestAnimationFrame||h.mozRequestAnimationFrame||h.webkitRequestAnimationFrame||h.msRequestAnimationFrame||function(e){setTimeout(e,0)})}},moduleExists:function(e){return p.fn[e]!==b&&p.fn[e].settings!==b},enabled:{modules:function(e){var n=[];return e=e||u.modules,p.each(e,function(e,t){s.moduleExists(t)&&n.push(t)}),n}},disabled:{modules:function(e){var n=[];return e=e||u.modules,p.each(e,function(e,t){s.moduleExists(t)||n.push(t)}),n}},change:{setting:function(o,a,e,r){e="string"==typeof e?"all"===e?u.modules:[e]:e||u.modules,r=r===b||r,p.each(e,function(e,t){var n,i=!s.moduleExists(t)||(p.fn[t].settings.namespace||!1);s.moduleExists(t)&&(s.verbose("Changing default setting",o,a,t),p.fn[t].settings[o]=a,r&&i&&0<(n=p(":data(module-"+i+")")).length&&(s.verbose("Modifying existing settings",n),n[t]("setting",o,a)))})},settings:function(i,e,o){e="string"==typeof e?[e]:e||u.modules,o=o===b||o,p.each(e,function(e,t){var n;s.moduleExists(t)&&(s.verbose("Changing default setting",i,t),p.extend(!0,p.fn[t].settings,i),o&&a&&0<(n=p(":data(module-"+a+")")).length&&(s.verbose("Modifying existing settings",n),n[t]("setting",i)))})}},enable:{console:function(){s.console(!0)},debug:function(e,t){e=e||u.modules,s.debug("Enabling debug for modules",e),s.change.setting("debug",!0,e,t)},verbose:function(e,t){e=e||u.modules,s.debug("Enabling verbose debug for modules",e),s.change.setting("verbose",!0,e,t)}},disable:{console:function(){s.console(!1)},debug:function(e,t){e=e||u.modules,s.debug("Disabling debug for modules",e),s.change.setting("debug",!1,e,t)},verbose:function(e,t){e=e||u.modules,s.debug("Disabling verbose debug for modules",e),s.change.setting("verbose",!1,e,t)}},console:function(e){if(e){if(g.cache.console===b)return void s.error(d.console);s.debug("Restoring console function"),h.console=g.cache.console}else s.debug("Disabling console function"),g.cache.console=h.console,h.console={clear:function(){},error:function(){},group:function(){},groupCollapsed:function(){},groupEnd:function(){},info:function(){},log:function(){},markTimeline:function(){},warn:function(){}}},destroy:function(){s.verbose("Destroying previous site for",f),f.removeData(r)},cache:{},setting:function(e,t){if(p.isPlainObject(e))p.extend(!0,u,e);else{if(t===b)return u[e];u[e]=t}},internal:function(e,t){if(p.isPlainObject(e))p.extend(!0,s,e);else{if(t===b)return s[e];s[e]=t}},debug:function(){u.debug&&(u.performance?s.performance.log(arguments):(s.debug=Function.prototype.bind.call(console.info,console,u.name+":"),s.debug.apply(console,arguments)))},verbose:function(){u.verbose&&u.debug&&(u.performance?s.performance.log(arguments):(s.verbose=Function.prototype.bind.call(console.info,console,u.name+":"),s.verbose.apply(console,arguments)))},error:function(){s.error=Function.prototype.bind.call(console.error,console,u.name+":"),s.error.apply(console,arguments)},performance:{log:function(e){var t,n;u.performance&&(n=(t=(new Date).getTime())-(i||t),i=t,o.push({Element:m,Name:e[0],Arguments:[].slice.call(e,1)||"","Execution Time":n})),clearTimeout(s.performance.timer),s.performance.timer=setTimeout(s.performance.display,500)},display:function(){var e=u.name+":",n=0;i=!1,clearTimeout(s.performance.timer),p.each(o,function(e,t){n+=t["Execution Time"]}),e+=" "+n+"ms",(console.group!==b||console.table!==b)&&0<o.length&&(console.groupCollapsed(e),console.table?console.table(o):p.each(o,function(e,t){console.log(t.Name+": "+t["Execution Time"]+"ms")}),console.groupEnd()),o=[]}},invoke:function(i,e,t){var o,a,n,r=g;return e=e||c,t=m||t,"string"==typeof i&&r!==b&&(i=i.split(/[\. ]/),o=i.length-1,p.each(i,function(e,t){var n=e!=o?t+i[e+1].charAt(0).toUpperCase()+i[e+1].slice(1):i;if(p.isPlainObject(r[n])&&e!=o)r=r[n];else{if(r[n]!==b)return a=r[n],!1;if(!p.isPlainObject(r[t])||e==o)return r[t]!==b?a=r[t]:s.error(d.method,i),!1;r=r[t]}})),p.isFunction(a)?n=a.apply(t,e):a!==b&&(n=a),p.isArray(l)?l.push(n):l!==b?l=[l,n]:n!==b&&(l=n),a}},n?(g===b&&s.initialize(),s.invoke(t)):(g!==b&&s.destroy(),s.initialize()),l!==b?l:this},p.site.settings={name:"Site",namespace:"site",error:{console:"Console cannot be restored, most likely it was overwritten outside of module",method:"The method you called is not defined."},debug:!1,verbose:!1,performance:!0,modules:["accordion","api","checkbox","dimmer","dropdown","embed","form","modal","nag","popup","rating","shape","sidebar","state","sticky","tab","transition","visit","visibility"],siteNamespace:"site",namespaceStub:{cache:{},config:{},sections:{},section:{},utilities:{}}},p.extend(p.expr[":"],{data:p.expr.createPseudo?p.expr.createPseudo(function(t){return function(e){return!!p.data(e,t)}}):function(e,t,n){return!!p.data(e,n[3])}})}(jQuery,window,document),function(F,e,O,D){"use strict";e=void 0!==e&&e.Math==Math?e:"undefined"!=typeof self&&self.Math==Math?self:Function("return this")(),F.fn.form=function(x){var C,w=F(this),S=w.selector||"",k=(new Date).getTime(),T=[],A=x,R=arguments[1],P="string"==typeof A,E=[].slice.call(arguments,1);return w.each(function(){var n,l,t,e,d,c,u,f,m,i,s,o,a,g,p,h,r=F(this),v=this,b=[],y=!1;(h={initialize:function(){h.get.settings(),P?(p===D&&h.instantiate(),h.invoke(A)):(p!==D&&p.invoke("destroy"),h.verbose("Initializing form validation",r,d),h.bindEvents(),h.set.defaults(),h.instantiate())},instantiate:function(){h.verbose("Storing instance of module",h),p=h,r.data(a,h)},destroy:function(){h.verbose("Destroying previous module",p),h.removeEvents(),r.removeData(a)},refresh:function(){h.verbose("Refreshing selector cache"),n=r.find(f.field),l=r.find(f.group),t=r.find(f.message),r.find(f.prompt),e=r.find(f.submit),r.find(f.clear),r.find(f.reset)},submit:function(){h.verbose("Submitting form",r),r.submit()},attachEvents:function(e,t){t=t||"submit",F(e).on("click"+g,function(e){h[t](),e.preventDefault()})},bindEvents:function(){h.verbose("Attaching form events"),r.on("submit"+g,h.validate.form).on("blur"+g,f.field,h.event.field.blur).on("click"+g,f.submit,h.submit).on("click"+g,f.reset,h.reset).on("click"+g,f.clear,h.clear),d.keyboardShortcuts&&r.on("keydown"+g,f.field,h.event.field.keydown),n.each(function(){var e=F(this),t=e.prop("type"),n=h.get.changeEvent(t,e);F(this).on(n+g,h.event.field.change)})},clear:function(){n.each(function(){var e=F(this),t=e.parent(),n=e.closest(l),i=n.find(f.prompt),o=e.data(u.defaultValue)||"",a=t.is(f.uiCheckbox),r=t.is(f.uiDropdown);n.hasClass(m.error)&&(h.verbose("Resetting error on field",n),n.removeClass(m.error),i.remove()),r?(h.verbose("Resetting dropdown value",t,o),t.dropdown("clear")):a?e.prop("checked",!1):(h.verbose("Resetting field value",e,o),e.val(""))})},reset:function(){n.each(function(){var e=F(this),t=e.parent(),n=e.closest(l),i=n.find(f.prompt),o=e.data(u.defaultValue),a=t.is(f.uiCheckbox),r=t.is(f.uiDropdown),s=n.hasClass(m.error);o!==D&&(s&&(h.verbose("Resetting error on field",n),n.removeClass(m.error),i.remove()),r?(h.verbose("Resetting dropdown value",t,o),t.dropdown("restore defaults")):a?(h.verbose("Resetting checkbox value",t,o),e.prop("checked",o)):(h.verbose("Resetting field value",e,o),e.val(o)))})},determine:{isValid:function(){var n=!0;return F.each(c,function(e,t){h.validate.field(t,e,!0)||(n=!1)}),n}},is:{bracketedRule:function(e){return e.type&&e.type.match(d.regExp.bracket)},shorthandFields:function(e){var t=e[Object.keys(e)[0]];return h.is.shorthandRules(t)},shorthandRules:function(e){return"string"==typeof e||F.isArray(e)},empty:function(e){return!e||0===e.length||(e.is('input[type="checkbox"]')?!e.is(":checked"):h.is.blank(e))},blank:function(e){return""===F.trim(e.val())},valid:function(e){var n=!0;return e?(h.verbose("Checking if field is valid",e),h.validate.field(c[e],e,!1)):(h.verbose("Checking if form is valid"),F.each(c,function(e,t){h.is.valid(e)||(n=!1)}),n)}},removeEvents:function(){r.off(g),n.off(g),e.off(g),n.off(g)},event:{field:{keydown:function(e){var t=F(this),n=e.which,i=t.is(f.input),o=t.is(f.checkbox),a=0<t.closest(f.uiDropdown).length,r=13;n==27&&(h.verbose("Escape key pressed blurring field"),t.blur()),e.ctrlKey||n!=r||!i||a||o||(y||(t.one("keyup"+g,h.event.field.keyup),h.submit(),h.debug("Enter pressed on input submitting form")),y=!0)},keyup:function(){y=!1},blur:function(e){var t=F(this),n=t.closest(l),i=h.get.validation(t);n.hasClass(m.error)?(h.debug("Revalidating field",t,i),i&&h.validate.field(i)):"blur"==d.on&&i&&h.validate.field(i)},change:function(e){var t=F(this),n=t.closest(l),i=h.get.validation(t);i&&("change"==d.on||n.hasClass(m.error)&&d.revalidate)&&(clearTimeout(h.timer),h.timer=setTimeout(function(){h.debug("Revalidating field",t,h.get.validation(t)),h.validate.field(i)},d.delay))}}},get:{ancillaryValue:function(e){return!(!e.type||!e.value&&!h.is.bracketedRule(e))&&(e.value!==D?e.value:e.type.match(d.regExp.bracket)[1]+"")},ruleName:function(e){return h.is.bracketedRule(e)?e.type.replace(e.type.match(d.regExp.bracket)[0],""):e.type},changeEvent:function(e,t){return"checkbox"==e||"radio"==e||"hidden"==e||t.is("select")?"change":h.get.inputEvent()},inputEvent:function(){return O.createElement("input").oninput!==D?"input":O.createElement("input").onpropertychange!==D?"propertychange":"keyup"},fieldsFromShorthand:function(e){var i={};return F.each(e,function(n,e){"string"==typeof e&&(e=[e]),i[n]={rules:[]},F.each(e,function(e,t){i[n].rules.push({type:t})})}),i},prompt:function(e,t){var n,i,o=h.get.ruleName(e),a=h.get.ancillaryValue(e),r=h.get.field(t.identifier),s=r.val(),l=F.isFunction(e.prompt)?e.prompt(s):e.prompt||d.prompt[o]||d.text.unspecifiedRule,c=-1!==l.search("{value}"),u=-1!==l.search("{name}");return c&&(l=l.replace("{value}",r.val())),u&&(i=1==(n=r.closest(f.group).find("label").eq(0)).length?n.text():r.prop("placeholder")||d.text.unspecifiedField,l=l.replace("{name}",i)),l=(l=l.replace("{identifier}",t.identifier)).replace("{ruleValue}",a),e.prompt||h.verbose("Using default validation prompt for type",l,o),l},settings:function(){if(F.isPlainObject(x)){var e=Object.keys(x);0<e.length&&(x[e[0]].identifier!==D&&x[e[0]].rules!==D)?(d=F.extend(!0,{},F.fn.form.settings,R),c=F.extend({},F.fn.form.settings.defaults,x),h.error(d.error.oldSyntax,v),h.verbose("Extending settings from legacy parameters",c,d)):(x.fields&&h.is.shorthandFields(x.fields)&&(x.fields=h.get.fieldsFromShorthand(x.fields)),d=F.extend(!0,{},F.fn.form.settings,x),c=F.extend({},F.fn.form.settings.defaults,d.fields),h.verbose("Extending settings",c,d))}else d=F.fn.form.settings,c=F.fn.form.settings.defaults,h.verbose("Using default form validation",c,d);o=d.namespace,u=d.metadata,f=d.selector,m=d.className,i=d.regExp,s=d.error,a="module-"+o,g="."+o,p=r.data(a),h.refresh()},field:function(e){return h.verbose("Finding field with identifier",e),e=h.escape.string(e),0<n.filter("#"+e).length?n.filter("#"+e):0<n.filter('[name="'+e+'"]').length?n.filter('[name="'+e+'"]'):0<n.filter('[name="'+e+'[]"]').length?n.filter('[name="'+e+'[]"]'):0<n.filter("[data-"+u.validate+'="'+e+'"]').length?n.filter("[data-"+u.validate+'="'+e+'"]'):F("<input/>")},fields:function(e){var n=F();return F.each(e,function(e,t){n=n.add(h.get.field(t))}),n},validation:function(n){var i,o;return!!c&&(F.each(c,function(e,t){o=t.identifier||e,h.get.field(o)[0]==n[0]&&(t.identifier=o,i=t)}),i||!1)},value:function(e){var t=[];return t.push(e),h.get.values.call(v,t)[e]},values:function(e){var t=F.isArray(e)?h.get.fields(e):n,c={};return t.each(function(e,t){var n=F(t),i=(n.prop("type"),n.prop("name")),o=n.val(),a=n.is(f.checkbox),r=n.is(f.radio),s=-1!==i.indexOf("[]"),l=!!a&&n.is(":checked");i&&(s?(i=i.replace("[]",""),c[i]||(c[i]=[]),a?l?c[i].push(o||!0):c[i].push(!1):c[i].push(o)):r?c[i]!==D&&0!=c[i]||(c[i]=!!l&&(o||!0)):c[i]=a?!!l&&(o||!0):o)}),c}},has:{field:function(e){return h.verbose("Checking for existence of a field with identifier",e),"string"!=typeof(e=h.escape.string(e))&&h.error(s.identifier,e),0<n.filter("#"+e).length||(0<n.filter('[name="'+e+'"]').length||0<n.filter("[data-"+u.validate+'="'+e+'"]').length)}},escape:{string:function(e){return(e=String(e)).replace(i.escape,"\\$&")}},add:{rule:function(e,t){h.add.field(e,t)},field:function(n,e){var i={};h.is.shorthandRules(e)?(e=F.isArray(e)?e:[e],i[n]={rules:[]},F.each(e,function(e,t){i[n].rules.push({type:t})})):i[n]=e,c=F.extend({},c,i),h.debug("Adding rules",i,c)},fields:function(e){var t;t=e&&h.is.shorthandFields(e)?h.get.fieldsFromShorthand(e):e,c=F.extend({},c,t)},prompt:function(e,t){var n=h.get.field(e).closest(l),i=n.children(f.prompt),o=0!==i.length;t="string"==typeof t?[t]:t,h.verbose("Adding field error state",e),n.addClass(m.error),d.inline&&(o||(i=d.templates.prompt(t)).appendTo(n),i.html(t[0]),o?h.verbose("Inline errors are disabled, no inline error added",e):d.transition&&F.fn.transition!==D&&r.transition("is supported")?(h.verbose("Displaying error with css transition",d.transition),i.transition(d.transition+" in",d.duration)):(h.verbose("Displaying error with fallback javascript animation"),i.fadeIn(d.duration)))},errors:function(e){h.debug("Adding form error messages",e),h.set.error(),t.html(d.templates.error(e))}},remove:{rule:function(n,e){var i=F.isArray(e)?e:[e];if(e==D)return h.debug("Removed all rules"),void(c[n].rules=[]);c[n]!=D&&F.isArray(c[n].rules)&&F.each(c[n].rules,function(e,t){-1!==i.indexOf(t.type)&&(h.debug("Removed rule",t.type),c[n].rules.splice(e,1))})},field:function(e){var t=F.isArray(e)?e:[e];F.each(t,function(e,t){h.remove.rule(t)})},rules:function(e,n){F.isArray(e)?F.each(fields,function(e,t){h.remove.rule(t,n)}):h.remove.rule(e,n)},fields:function(e){h.remove.field(e)},prompt:function(e){var t=h.get.field(e).closest(l),n=t.children(f.prompt);t.removeClass(m.error),d.inline&&n.is(":visible")&&(h.verbose("Removing prompt for field",e),d.transition&&F.fn.transition!==D&&r.transition("is supported")?n.transition(d.transition+" out",d.duration,function(){n.remove()}):n.fadeOut(d.duration,function(){n.remove()}))}},set:{success:function(){r.removeClass(m.error).addClass(m.success)},defaults:function(){n.each(function(){var e=F(this),t=0<e.filter(f.checkbox).length?e.is(":checked"):e.val();e.data(u.defaultValue,t)})},error:function(){r.removeClass(m.success).addClass(m.error)},value:function(e,t){var n={};return n[e]=t,h.set.values.call(v,n)},values:function(e){F.isEmptyObject(e)||F.each(e,function(e,t){var n,i=h.get.field(e),o=i.parent(),a=F.isArray(t),r=o.is(f.uiCheckbox),s=o.is(f.uiDropdown),l=i.is(f.radio)&&r;0<i.length&&(a&&r?(h.verbose("Selecting multiple",t,i),o.checkbox("uncheck"),F.each(t,function(e,t){n=i.filter('[value="'+t+'"]'),o=n.parent(),0<n.length&&o.checkbox("check")})):l?(h.verbose("Selecting radio value",t,i),i.filter('[value="'+t+'"]').parent(f.uiCheckbox).checkbox("check")):r?(h.verbose("Setting checkbox value",t,o),!0===t?o.checkbox("check"):o.checkbox("uncheck")):s?(h.verbose("Setting dropdown value",t,o),o.dropdown("set selected",t)):(h.verbose("Setting field value",t,i),i.val(t)))})}},validate:{form:function(e,t){var n=h.get.values();if(y)return!1;if(b=[],h.determine.isValid()){if(h.debug("Form has no validation errors, submitting"),h.set.success(),!0!==t)return d.onSuccess.call(v,e,n)}else if(h.debug("Form has errors"),h.set.error(),d.inline||h.add.errors(b),r.data("moduleApi")!==D&&e.stopImmediatePropagation(),!0!==t)return d.onFailure.call(v,b,n)},field:function(n,e,t){t=t===D||t,"string"==typeof n&&(h.verbose("Validating field",n),n=c[e=n]);var i=n.identifier||e,o=h.get.field(i),a=!!n.depends&&h.get.field(n.depends),r=!0,s=[];return n.identifier||(h.debug("Using field name as identifier",i),n.identifier=i),o.prop("disabled")?(h.debug("Field is disabled. Skipping",i),r=!0):n.optional&&h.is.blank(o)?(h.debug("Field is optional and blank. Skipping",i),r=!0):n.depends&&h.is.empty(a)?(h.debug("Field depends on another value that is not present or empty. Skipping",a),r=!0):n.rules!==D&&F.each(n.rules,function(e,t){h.has.field(i)&&!h.validate.rule(n,t)&&(h.debug("Field is invalid",i,t.type),s.push(h.get.prompt(t,n)),r=!1)}),r?(t&&(h.remove.prompt(i,s),d.onValid.call(o)),!0):(t&&(b=b.concat(s),h.add.prompt(i,s),d.onInvalid.call(o,s)),!1)},rule:function(e,t){var n=h.get.field(e.identifier),i=(t.type,n.val()),o=h.get.ancillaryValue(t),a=h.get.ruleName(t),r=d.rules[a];if(F.isFunction(r))return i=i===D||""===i||null===i?"":F.trim(i+""),r.call(n,i,o);h.error(s.noRule,a)}},setting:function(e,t){if(F.isPlainObject(e))F.extend(!0,d,e);else{if(t===D)return d[e];d[e]=t}},internal:function(e,t){if(F.isPlainObject(e))F.extend(!0,h,e);else{if(t===D)return h[e];h[e]=t}},debug:function(){!d.silent&&d.debug&&(d.performance?h.performance.log(arguments):(h.debug=Function.prototype.bind.call(console.info,console,d.name+":"),h.debug.apply(console,arguments)))},verbose:function(){!d.silent&&d.verbose&&d.debug&&(d.performance?h.performance.log(arguments):(h.verbose=Function.prototype.bind.call(console.info,console,d.name+":"),h.verbose.apply(console,arguments)))},error:function(){d.silent||(h.error=Function.prototype.bind.call(console.error,console,d.name+":"),h.error.apply(console,arguments))},performance:{log:function(e){var t,n;d.performance&&(n=(t=(new Date).getTime())-(k||t),k=t,T.push({Name:e[0],Arguments:[].slice.call(e,1)||"",Element:v,"Execution Time":n})),clearTimeout(h.performance.timer),h.performance.timer=setTimeout(h.performance.display,500)},display:function(){var e=d.name+":",n=0;k=!1,clearTimeout(h.performance.timer),F.each(T,function(e,t){n+=t["Execution Time"]}),e+=" "+n+"ms",S&&(e+=" '"+S+"'"),1<w.length&&(e+=" ("+w.length+")"),(console.group!==D||console.table!==D)&&0<T.length&&(console.groupCollapsed(e),console.table?console.table(T):F.each(T,function(e,t){console.log(t.Name+": "+t["Execution Time"]+"ms")}),console.groupEnd()),T=[]}},invoke:function(i,e,t){var o,a,n,r=p;return e=e||E,t=v||t,"string"==typeof i&&r!==D&&(i=i.split(/[\. ]/),o=i.length-1,F.each(i,function(e,t){var n=e!=o?t+i[e+1].charAt(0).toUpperCase()+i[e+1].slice(1):i;if(F.isPlainObject(r[n])&&e!=o)r=r[n];else{if(r[n]!==D)return a=r[n],!1;if(!F.isPlainObject(r[t])||e==o)return r[t]!==D&&(a=r[t]),!1;r=r[t]}})),F.isFunction(a)?n=a.apply(t,e):a!==D&&(n=a),F.isArray(C)?C.push(n):C!==D?C=[C,n]:n!==D&&(C=n),a}}).initialize()}),C!==D?C:this},F.fn.form.settings={name:"Form",namespace:"form",debug:!1,verbose:!1,performance:!0,fields:!1,keyboardShortcuts:!0,on:"submit",inline:!1,delay:200,revalidate:!0,transition:"scale",duration:200,onValid:function(){},onInvalid:function(){},onSuccess:function(){return!0},onFailure:function(){return!1},metadata:{defaultValue:"default",validate:"validate"},regExp:{htmlID:/^[a-zA-Z][\w:.-]*$/g,bracket:/\[(.*)\]/i,decimal:/^\d+\.?\d*$/,email:/^[a-z0-9!#$%&'*+\/=?^_`{|}~.-]+@[a-z0-9]([a-z0-9-]*[a-z0-9])?(\.[a-z0-9]([a-z0-9-]*[a-z0-9])?)*$/i,escape:/[\-\[\]\/\{\}\(\)\*\+\?\.\\\^\$\|]/g,flags:/^\/(.*)\/(.*)?/,integer:/^\-?\d+$/,number:/^\-?\d*(\.\d+)?$/,url:/(https?:\/\/(?:www\.|(?!www))[^\s\.]+\.[^\s]{2,}|www\.[^\s]+\.[^\s]{2,})/i},text:{unspecifiedRule:"Please enter a valid value",unspecifiedField:"This field"},prompt:{empty:"{name} must have a value",checked:"{name} must be checked",email:"{name} must be a valid e-mail",url:"{name} must be a valid url",regExp:"{name} is not formatted correctly",integer:"{name} must be an integer",decimal:"{name} must be a decimal number",number:"{name} must be set to a number",is:'{name} must be "{ruleValue}"',isExactly:'{name} must be exactly "{ruleValue}"',not:'{name} cannot be set to "{ruleValue}"',notExactly:'{name} cannot be set to exactly "{ruleValue}"',contain:'{name} must contain "{ruleValue}"',containExactly:'{name} must contain exactly "{ruleValue}"',doesntContain:'{name} cannot contain "{ruleValue}"',doesntContainExactly:'{name} cannot contain exactly "{ruleValue}"',minLength:"{name} must be at least {ruleValue} characters",length:"{name} must be at least {ruleValue} characters",exactLength:"{name} must be exactly {ruleValue} characters",maxLength:"{name} cannot be longer than {ruleValue} characters",match:"{name} must match {ruleValue} field",different:"{name} must have a different value than {ruleValue} field",creditCard:"{name} must be a valid credit card number",minCount:"{name} must have at least {ruleValue} choices",exactCount:"{name} must have exactly {ruleValue} choices",maxCount:"{name} must have {ruleValue} or less choices"},selector:{checkbox:'input[type="checkbox"], input[type="radio"]',clear:".clear",field:"input, textarea, select",group:".field",input:"input",message:".error.message",prompt:".prompt.label",radio:'input[type="radio"]',reset:'.reset:not([type="reset"])',submit:'.submit:not([type="submit"])',uiCheckbox:".ui.checkbox",uiDropdown:".ui.dropdown"},className:{error:"error",label:"ui prompt label",pressed:"down",success:"success"},error:{identifier:"You must specify a string identifier for each field",method:"The method you called is not defined.",noRule:"There is no rule matching the one you specified",oldSyntax:"Starting in 2.0 forms now only take a single settings object. Validation settings converted to new syntax automatically."},templates:{error:function(e){var n='<ul class="list">';return F.each(e,function(e,t){n+="<li>"+t+"</li>"}),F(n+="</ul>")},prompt:function(e){return F("<div/>").addClass("ui basic red pointing prompt label").html(e[0])}},rules:{empty:function(e){return!(e===D||""===e||F.isArray(e)&&0===e.length)},checked:function(){return 0<F(this).filter(":checked").length},email:function(e){return F.fn.form.settings.regExp.email.test(e)},url:function(e){return F.fn.form.settings.regExp.url.test(e)},regExp:function(e,t){if(t instanceof RegExp)return e.match(t);var n,i=t.match(F.fn.form.settings.regExp.flags);return i&&(t=2<=i.length?i[1]:t,n=3<=i.length?i[2]:""),e.match(new RegExp(t,n))},integer:function(e,t){var n,i,o,a=F.fn.form.settings.regExp.integer;return t&&-1===["",".."].indexOf(t)&&(-1==t.indexOf("..")?a.test(t)&&(n=i=t-0):(o=t.split("..",2),a.test(o[0])&&(n=o[0]-0),a.test(o[1])&&(i=o[1]-0))),a.test(e)&&(n===D||n<=e)&&(i===D||e<=i)},decimal:function(e){return F.fn.form.settings.regExp.decimal.test(e)},number:function(e){return F.fn.form.settings.regExp.number.test(e)},is:function(e,t){return t="string"==typeof t?t.toLowerCase():t,(e="string"==typeof e?e.toLowerCase():e)==t},isExactly:function(e,t){return e==t},not:function(e,t){return(e="string"==typeof e?e.toLowerCase():e)!=(t="string"==typeof t?t.toLowerCase():t)},notExactly:function(e,t){return e!=t},contains:function(e,t){return t=t.replace(F.fn.form.settings.regExp.escape,"\\$&"),-1!==e.search(new RegExp(t,"i"))},containsExactly:function(e,t){return t=t.replace(F.fn.form.settings.regExp.escape,"\\$&"),-1!==e.search(new RegExp(t))},doesntContain:function(e,t){return t=t.replace(F.fn.form.settings.regExp.escape,"\\$&"),-1===e.search(new RegExp(t,"i"))},doesntContainExactly:function(e,t){return t=t.replace(F.fn.form.settings.regExp.escape,"\\$&"),-1===e.search(new RegExp(t))},minLength:function(e,t){return e!==D&&e.length>=t},length:function(e,t){return e!==D&&e.length>=t},exactLength:function(e,t){return e!==D&&e.length==t},maxLength:function(e,t){return e!==D&&e.length<=t},match:function(e,t){var n;F(this);return 0<F('[data-validate="'+t+'"]').length?n=F('[data-validate="'+t+'"]').val():0<F("#"+t).length?n=F("#"+t).val():0<F('[name="'+t+'"]').length?n=F('[name="'+t+'"]').val():0<F('[name="'+t+'[]"]').length&&(n=F('[name="'+t+'[]"]')),n!==D&&e.toString()==n.toString()},different:function(e,t){var n;F(this);return 0<F('[data-validate="'+t+'"]').length?n=F('[data-validate="'+t+'"]').val():0<F("#"+t).length?n=F("#"+t).val():0<F('[name="'+t+'"]').length?n=F('[name="'+t+'"]').val():0<F('[name="'+t+'[]"]').length&&(n=F('[name="'+t+'[]"]')),n!==D&&e.toString()!==n.toString()},creditCard:function(n,e){var t,i,o={visa:{pattern:/^4/,length:[16]},amex:{pattern:/^3[47]/,length:[15]},mastercard:{pattern:/^5[1-5]/,length:[16]},discover:{pattern:/^(6011|622(12[6-9]|1[3-9][0-9]|[2-8][0-9]{2}|9[0-1][0-9]|92[0-5]|64[4-9])|65)/,length:[16]},unionPay:{pattern:/^(62|88)/,length:[16,17,18,19]},jcb:{pattern:/^35(2[89]|[3-8][0-9])/,length:[16]},maestro:{pattern:/^(5018|5020|5038|6304|6759|676[1-3])/,length:[12,13,14,15,16,17,18,19]},dinersClub:{pattern:/^(30[0-5]|^36)/,length:[14]},laser:{pattern:/^(6304|670[69]|6771)/,length:[16,17,18,19]},visaElectron:{pattern:/^(4026|417500|4508|4844|491(3|7))/,length:[16]}},a={},r=!1,s="string"==typeof e&&e.split(",");if("string"==typeof n&&0!==n.length){if(n=n.replace(/[\-]/g,""),s&&(F.each(s,function(e,t){(i=o[t])&&(a={length:-1!==F.inArray(n.length,i.length),pattern:-1!==n.search(i.pattern)}).length&&a.pattern&&(r=!0)}),!r))return!1;if((t={number:-1!==F.inArray(n.length,o.unionPay.length),pattern:-1!==n.search(o.unionPay.pattern)}).number&&t.pattern)return!0;for(var l=n.length,c=0,u=[[0,1,2,3,4,5,6,7,8,9],[0,2,4,6,8,1,3,5,7,9]],d=0;l--;)d+=u[c][parseInt(n.charAt(l),10)],c^=1;return d%10==0&&0<d}},minCount:function(e,t){return 0==t||(1==t?""!==e:e.split(",").length>=t)},exactCount:function(e,t){return 0==t?""===e:1==t?""!==e&&-1===e.search(","):e.split(",").length==t},maxCount:function(e,t){return 0!=t&&(1==t?-1===e.search(","):e.split(",").length<=t)}}}}(jQuery,window,document),function(S,k,e,T){"use strict";k=void 0!==k&&k.Math==Math?k:"undefined"!=typeof self&&self.Math==Math?self:Function("return this")(),S.fn.accordion=function(a){var v,r=S(this),b=(new Date).getTime(),y=[],x=a,C="string"==typeof x,w=[].slice.call(arguments,1);k.requestAnimationFrame||k.mozRequestAnimationFrame||k.webkitRequestAnimationFrame||k.msRequestAnimationFrame;return r.each(function(){var e,c,u=S.isPlainObject(a)?S.extend(!0,{},S.fn.accordion.settings,a):S.extend({},S.fn.accordion.settings),d=u.className,t=u.namespace,f=u.selector,s=u.error,n="."+t,i="module-"+t,o=r.selector||"",m=S(this),g=m.find(f.title),p=m.find(f.content),l=this,h=m.data(i);c={initialize:function(){c.debug("Initializing",m),c.bind.events(),u.observeChanges&&c.observeChanges(),c.instantiate()},instantiate:function(){h=c,m.data(i,c)},destroy:function(){c.debug("Destroying previous instance",m),m.off(n).removeData(i)},refresh:function(){g=m.find(f.title),p=m.find(f.content)},observeChanges:function(){"MutationObserver"in k&&((e=new MutationObserver(function(e){c.debug("DOM tree modified, updating selector cache"),c.refresh()})).observe(l,{childList:!0,subtree:!0}),c.debug("Setting up mutation observer",e))},bind:{events:function(){c.debug("Binding delegated events"),m.on(u.on+n,f.trigger,c.event.click)}},event:{click:function(){c.toggle.call(this)}},toggle:function(e){var t=e!==T?"number"==typeof e?g.eq(e):S(e).closest(f.title):S(this).closest(f.title),n=t.next(p),i=n.hasClass(d.animating),o=n.hasClass(d.active),a=o&&!i,r=!o&&i;c.debug("Toggling visibility of content",t),a||r?u.collapsible?c.close.call(t):c.debug("Cannot close accordion content collapsing is disabled"):c.open.call(t)},open:function(e){var t=e!==T?"number"==typeof e?g.eq(e):S(e).closest(f.title):S(this).closest(f.title),n=t.next(p),i=n.hasClass(d.animating);n.hasClass(d.active)||i?c.debug("Accordion already open, skipping",n):(c.debug("Opening accordion content",t),u.onOpening.call(n),u.onChanging.call(n),u.exclusive&&c.closeOthers.call(t),t.addClass(d.active),n.stop(!0,!0).addClass(d.animating),u.animateChildren&&(S.fn.transition!==T&&m.transition("is supported")?n.children().transition({animation:"fade in",queue:!1,useFailSafe:!0,debug:u.debug,verbose:u.verbose,duration:u.duration}):n.children().stop(!0,!0).animate({opacity:1},u.duration,c.resetOpacity)),n.slideDown(u.duration,u.easing,function(){n.removeClass(d.animating).addClass(d.active),c.reset.display.call(this),u.onOpen.call(this),u.onChange.call(this)}))},close:function(e){var t=e!==T?"number"==typeof e?g.eq(e):S(e).closest(f.title):S(this).closest(f.title),n=t.next(p),i=n.hasClass(d.animating),o=n.hasClass(d.active);!o&&!(!o&&i)||o&&i||(c.debug("Closing accordion content",n),u.onClosing.call(n),u.onChanging.call(n),t.removeClass(d.active),n.stop(!0,!0).addClass(d.animating),u.animateChildren&&(S.fn.transition!==T&&m.transition("is supported")?n.children().transition({animation:"fade out",queue:!1,useFailSafe:!0,debug:u.debug,verbose:u.verbose,duration:u.duration}):n.children().stop(!0,!0).animate({opacity:0},u.duration,c.resetOpacity)),n.slideUp(u.duration,u.easing,function(){n.removeClass(d.animating).removeClass(d.active),c.reset.display.call(this),u.onClose.call(this),u.onChange.call(this)}))},closeOthers:function(e){var t,n,i,o=e!==T?g.eq(e):S(this).closest(f.title),a=o.parents(f.content).prev(f.title),r=o.closest(f.accordion),s=f.title+"."+d.active+":visible",l=f.content+"."+d.active+":visible";i=u.closeNested?(t=r.find(s).not(a)).next(p):(t=r.find(s).not(a),n=r.find(l).find(s).not(a),(t=t.not(n)).next(p)),0<t.length&&(c.debug("Exclusive enabled, closing other content",t),t.removeClass(d.active),i.removeClass(d.animating).stop(!0,!0),u.animateChildren&&(S.fn.transition!==T&&m.transition("is supported")?i.children().transition({animation:"fade out",useFailSafe:!0,debug:u.debug,verbose:u.verbose,duration:u.duration}):i.children().stop(!0,!0).animate({opacity:0},u.duration,c.resetOpacity)),i.slideUp(u.duration,u.easing,function(){S(this).removeClass(d.active),c.reset.display.call(this)}))},reset:{display:function(){c.verbose("Removing inline display from element",this),S(this).css("display",""),""===S(this).attr("style")&&S(this).attr("style","").removeAttr("style")},opacity:function(){c.verbose("Removing inline opacity from element",this),S(this).css("opacity",""),""===S(this).attr("style")&&S(this).attr("style","").removeAttr("style")}},setting:function(e,t){if(c.debug("Changing setting",e,t),S.isPlainObject(e))S.extend(!0,u,e);else{if(t===T)return u[e];S.isPlainObject(u[e])?S.extend(!0,u[e],t):u[e]=t}},internal:function(e,t){if(c.debug("Changing internal",e,t),t===T)return c[e];S.isPlainObject(e)?S.extend(!0,c,e):c[e]=t},debug:function(){!u.silent&&u.debug&&(u.performance?c.performance.log(arguments):(c.debug=Function.prototype.bind.call(console.info,console,u.name+":"),c.debug.apply(console,arguments)))},verbose:function(){!u.silent&&u.verbose&&u.debug&&(u.performance?c.performance.log(arguments):(c.verbose=Function.prototype.bind.call(console.info,console,u.name+":"),c.verbose.apply(console,arguments)))},error:function(){u.silent||(c.error=Function.prototype.bind.call(console.error,console,u.name+":"),c.error.apply(console,arguments))},performance:{log:function(e){var t,n;u.performance&&(n=(t=(new Date).getTime())-(b||t),b=t,y.push({Name:e[0],Arguments:[].slice.call(e,1)||"",Element:l,"Execution Time":n})),clearTimeout(c.performance.timer),c.performance.timer=setTimeout(c.performance.display,500)},display:function(){var e=u.name+":",n=0;b=!1,clearTimeout(c.performance.timer),S.each(y,function(e,t){n+=t["Execution Time"]}),e+=" "+n+"ms",o&&(e+=" '"+o+"'"),(console.group!==T||console.table!==T)&&0<y.length&&(console.groupCollapsed(e),console.table?console.table(y):S.each(y,function(e,t){console.log(t.Name+": "+t["Execution Time"]+"ms")}),console.groupEnd()),y=[]}},invoke:function(i,e,t){var o,a,n,r=h;return e=e||w,t=l||t,"string"==typeof i&&r!==T&&(i=i.split(/[\. ]/),o=i.length-1,S.each(i,function(e,t){var n=e!=o?t+i[e+1].charAt(0).toUpperCase()+i[e+1].slice(1):i;if(S.isPlainObject(r[n])&&e!=o)r=r[n];else{if(r[n]!==T)return a=r[n],!1;if(!S.isPlainObject(r[t])||e==o)return r[t]!==T?a=r[t]:c.error(s.method,i),!1;r=r[t]}})),S.isFunction(a)?n=a.apply(t,e):a!==T&&(n=a),S.isArray(v)?v.push(n):v!==T?v=[v,n]:n!==T&&(v=n),a}},C?(h===T&&c.initialize(),c.invoke(x)):(h!==T&&h.invoke("destroy"),c.initialize())}),v!==T?v:this},S.fn.accordion.settings={name:"Accordion",namespace:"accordion",silent:!1,debug:!1,verbose:!1,performance:!0,on:"click",observeChanges:!0,exclusive:!0,collapsible:!0,closeNested:!1,animateChildren:!0,duration:350,easing:"easeOutQuad",onOpening:function(){},onClosing:function(){},onChanging:function(){},onOpen:function(){},onClose:function(){},onChange:function(){},error:{method:"The method you called is not defined"},className:{active:"active",animating:"animating"},selector:{accordion:".accordion",title:".title",trigger:".title",content:".content"}},S.extend(S.easing,{easeOutQuad:function(e,t,n,i,o){return-i*(t/=o)*(t-2)+n}})}(jQuery,window,document),function(T,A,R,P){"use strict";A=void 0!==A&&A.Math==Math?A:"undefined"!=typeof self&&self.Math==Math?self:Function("return this")(),T.fn.checkbox=function(v){var b,e=T(this),y=e.selector||"",x=(new Date).getTime(),C=[],w=v,S="string"==typeof w,k=[].slice.call(arguments,1);return e.each(function(){var e,s,i=T.extend(!0,{},T.fn.checkbox.settings,v),t=i.className,n=i.namespace,o=i.selector,l=i.error,a="."+n,r="module-"+n,c=T(this),u=T(this).children(o.label),d=T(this).children(o.input),f=d[0],m=!1,g=!1,p=c.data(r),h=this;s={initialize:function(){s.verbose("Initializing checkbox",i),s.create.label(),s.bind.events(),s.set.tabbable(),s.hide.input(),s.observeChanges(),s.instantiate(),s.setup()},instantiate:function(){s.verbose("Storing instance of module",s),p=s,c.data(r,s)},destroy:function(){s.verbose("Destroying module"),s.unbind.events(),s.show.input(),c.removeData(r)},fix:{reference:function(){c.is(o.input)&&(s.debug("Behavior called on <input> adjusting invoked element"),c=c.closest(o.checkbox),s.refresh())}},setup:function(){s.set.initialLoad(),s.is.indeterminate()?(s.debug("Initial value is indeterminate"),s.indeterminate()):s.is.checked()?(s.debug("Initial value is checked"),s.check()):(s.debug("Initial value is unchecked"),s.uncheck()),s.remove.initialLoad()},refresh:function(){u=c.children(o.label),d=c.children(o.input),f=d[0]},hide:{input:function(){s.verbose("Modifying <input> z-index to be unselectable"),d.addClass(t.hidden)}},show:{input:function(){s.verbose("Modifying <input> z-index to be selectable"),d.removeClass(t.hidden)}},observeChanges:function(){"MutationObserver"in A&&((e=new MutationObserver(function(e){s.debug("DOM tree modified, updating selector cache"),s.refresh()})).observe(h,{childList:!0,subtree:!0}),s.debug("Setting up mutation observer",e))},attachEvents:function(e,t){var n=T(e);t=T.isFunction(s[t])?s[t]:s.toggle,0<n.length?(s.debug("Attaching checkbox events to element",e,t),n.on("click"+a,t)):s.error(l.notFound)},event:{click:function(e){var t=T(e.target);t.is(o.input)?s.verbose("Using default check action on initialized checkbox"):t.is(o.link)?s.debug("Clicking link inside checkbox, skipping toggle"):(s.toggle(),d.focus(),e.preventDefault())},keydown:function(e){var t=e.which,n=13,i=32;g=t==27?(s.verbose("Escape key pressed blurring field"),d.blur(),!0):!(e.ctrlKey||t!=i&&t!=n)&&(s.verbose("Enter/space key pressed, toggling checkbox"),s.toggle(),!0)},keyup:function(e){g&&e.preventDefault()}},check:function(){s.should.allowCheck()&&(s.debug("Checking checkbox",d),s.set.checked(),s.should.ignoreCallbacks()||(i.onChecked.call(f),i.onChange.call(f)))},uncheck:function(){s.should.allowUncheck()&&(s.debug("Unchecking checkbox"),s.set.unchecked(),s.should.ignoreCallbacks()||(i.onUnchecked.call(f),i.onChange.call(f)))},indeterminate:function(){s.should.allowIndeterminate()?s.debug("Checkbox is already indeterminate"):(s.debug("Making checkbox indeterminate"),s.set.indeterminate(),s.should.ignoreCallbacks()||(i.onIndeterminate.call(f),i.onChange.call(f)))},determinate:function(){s.should.allowDeterminate()?s.debug("Checkbox is already determinate"):(s.debug("Making checkbox determinate"),s.set.determinate(),s.should.ignoreCallbacks()||(i.onDeterminate.call(f),i.onChange.call(f)))},enable:function(){s.is.enabled()?s.debug("Checkbox is already enabled"):(s.debug("Enabling checkbox"),s.set.enabled(),i.onEnable.call(f),i.onEnabled.call(f))},disable:function(){s.is.disabled()?s.debug("Checkbox is already disabled"):(s.debug("Disabling checkbox"),s.set.disabled(),i.onDisable.call(f),i.onDisabled.call(f))},get:{radios:function(){var e=s.get.name();return T('input[name="'+e+'"]').closest(o.checkbox)},otherRadios:function(){return s.get.radios().not(c)},name:function(){return d.attr("name")}},is:{initialLoad:function(){return m},radio:function(){return d.hasClass(t.radio)||"radio"==d.attr("type")},indeterminate:function(){return d.prop("indeterminate")!==P&&d.prop("indeterminate")},checked:function(){return d.prop("checked")!==P&&d.prop("checked")},disabled:function(){return d.prop("disabled")!==P&&d.prop("disabled")},enabled:function(){return!s.is.disabled()},determinate:function(){return!s.is.indeterminate()},unchecked:function(){return!s.is.checked()}},should:{allowCheck:function(){return s.is.determinate()&&s.is.checked()&&!s.should.forceCallbacks()?(s.debug("Should not allow check, checkbox is already checked"),!1):!1!==i.beforeChecked.apply(f)||(s.debug("Should not allow check, beforeChecked cancelled"),!1)},allowUncheck:function(){return s.is.determinate()&&s.is.unchecked()&&!s.should.forceCallbacks()?(s.debug("Should not allow uncheck, checkbox is already unchecked"),!1):!1!==i.beforeUnchecked.apply(f)||(s.debug("Should not allow uncheck, beforeUnchecked cancelled"),!1)},allowIndeterminate:function(){return s.is.indeterminate()&&!s.should.forceCallbacks()?(s.debug("Should not allow indeterminate, checkbox is already indeterminate"),!1):!1!==i.beforeIndeterminate.apply(f)||(s.debug("Should not allow indeterminate, beforeIndeterminate cancelled"),!1)},allowDeterminate:function(){return s.is.determinate()&&!s.should.forceCallbacks()?(s.debug("Should not allow determinate, checkbox is already determinate"),!1):!1!==i.beforeDeterminate.apply(f)||(s.debug("Should not allow determinate, beforeDeterminate cancelled"),!1)},forceCallbacks:function(){return s.is.initialLoad()&&i.fireOnInit},ignoreCallbacks:function(){return m&&!i.fireOnInit}},can:{change:function(){return!(c.hasClass(t.disabled)||c.hasClass(t.readOnly)||d.prop("disabled")||d.prop("readonly"))},uncheck:function(){return"boolean"==typeof i.uncheckable?i.uncheckable:!s.is.radio()}},set:{initialLoad:function(){m=!0},checked:function(){s.verbose("Setting class to checked"),c.removeClass(t.indeterminate).addClass(t.checked),s.is.radio()&&s.uncheckOthers(),s.is.indeterminate()||!s.is.checked()?(s.verbose("Setting state to checked",f),d.prop("indeterminate",!1).prop("checked",!0),s.trigger.change()):s.debug("Input is already checked, skipping input property change")},unchecked:function(){s.verbose("Removing checked class"),c.removeClass(t.indeterminate).removeClass(t.checked),s.is.indeterminate()||!s.is.unchecked()?(s.debug("Setting state to unchecked"),d.prop("indeterminate",!1).prop("checked",!1),s.trigger.change()):s.debug("Input is already unchecked")},indeterminate:function(){s.verbose("Setting class to indeterminate"),c.addClass(t.indeterminate),s.is.indeterminate()?s.debug("Input is already indeterminate, skipping input property change"):(s.debug("Setting state to indeterminate"),d.prop("indeterminate",!0),s.trigger.change())},determinate:function(){s.verbose("Removing indeterminate class"),c.removeClass(t.indeterminate),s.is.determinate()?s.debug("Input is already determinate, skipping input property change"):(s.debug("Setting state to determinate"),d.prop("indeterminate",!1))},disabled:function(){s.verbose("Setting class to disabled"),c.addClass(t.disabled),s.is.disabled()?s.debug("Input is already disabled, skipping input property change"):(s.debug("Setting state to disabled"),d.prop("disabled","disabled"),s.trigger.change())},enabled:function(){s.verbose("Removing disabled class"),c.removeClass(t.disabled),s.is.enabled()?s.debug("Input is already enabled, skipping input property change"):(s.debug("Setting state to enabled"),d.prop("disabled",!1),s.trigger.change())},tabbable:function(){s.verbose("Adding tabindex to checkbox"),d.attr("tabindex")===P&&d.attr("tabindex",0)}},remove:{initialLoad:function(){m=!1}},trigger:{change:function(){var e=R.createEvent("HTMLEvents"),t=d[0];t&&(s.verbose("Triggering native change event"),e.initEvent("change",!0,!1),t.dispatchEvent(e))}},create:{label:function(){0<d.prevAll(o.label).length?(d.prev(o.label).detach().insertAfter(d),s.debug("Moving existing label",u)):s.has.label()||(u=T("<label>").insertAfter(d),s.debug("Creating label",u))}},has:{label:function(){return 0<u.length}},bind:{events:function(){s.verbose("Attaching checkbox events"),c.on("click"+a,s.event.click).on("keydown"+a,o.input,s.event.keydown).on("keyup"+a,o.input,s.event.keyup)}},unbind:{events:function(){s.debug("Removing events"),c.off(a)}},uncheckOthers:function(){var e=s.get.otherRadios();s.debug("Unchecking other radios",e),e.removeClass(t.checked)},toggle:function(){s.can.change()?s.is.indeterminate()||s.is.unchecked()?(s.debug("Currently unchecked"),s.check()):s.is.checked()&&s.can.uncheck()&&(s.debug("Currently checked"),s.uncheck()):s.is.radio()||s.debug("Checkbox is read-only or disabled, ignoring toggle")},setting:function(e,t){if(s.debug("Changing setting",e,t),T.isPlainObject(e))T.extend(!0,i,e);else{if(t===P)return i[e];T.isPlainObject(i[e])?T.extend(!0,i[e],t):i[e]=t}},internal:function(e,t){if(T.isPlainObject(e))T.extend(!0,s,e);else{if(t===P)return s[e];s[e]=t}},debug:function(){!i.silent&&i.debug&&(i.performance?s.performance.log(arguments):(s.debug=Function.prototype.bind.call(console.info,console,i.name+":"),s.debug.apply(console,arguments)))},verbose:function(){!i.silent&&i.verbose&&i.debug&&(i.performance?s.performance.log(arguments):(s.verbose=Function.prototype.bind.call(console.info,console,i.name+":"),s.verbose.apply(console,arguments)))},error:function(){i.silent||(s.error=Function.prototype.bind.call(console.error,console,i.name+":"),s.error.apply(console,arguments))},performance:{log:function(e){var t,n;i.performance&&(n=(t=(new Date).getTime())-(x||t),x=t,C.push({Name:e[0],Arguments:[].slice.call(e,1)||"",Element:h,"Execution Time":n})),clearTimeout(s.performance.timer),s.performance.timer=setTimeout(s.performance.display,500)},display:function(){var e=i.name+":",n=0;x=!1,clearTimeout(s.performance.timer),T.each(C,function(e,t){n+=t["Execution Time"]}),e+=" "+n+"ms",y&&(e+=" '"+y+"'"),(console.group!==P||console.table!==P)&&0<C.length&&(console.groupCollapsed(e),console.table?console.table(C):T.each(C,function(e,t){console.log(t.Name+": "+t["Execution Time"]+"ms")}),console.groupEnd()),C=[]}},invoke:function(i,e,t){var o,a,n,r=p;return e=e||k,t=h||t,"string"==typeof i&&r!==P&&(i=i.split(/[\. ]/),o=i.length-1,T.each(i,function(e,t){var n=e!=o?t+i[e+1].charAt(0).toUpperCase()+i[e+1].slice(1):i;if(T.isPlainObject(r[n])&&e!=o)r=r[n];else{if(r[n]!==P)return a=r[n],!1;if(!T.isPlainObject(r[t])||e==o)return r[t]!==P?a=r[t]:s.error(l.method,i),!1;r=r[t]}})),T.isFunction(a)?n=a.apply(t,e):a!==P&&(n=a),T.isArray(b)?b.push(n):b!==P?b=[b,n]:n!==P&&(b=n),a}},S?(p===P&&s.initialize(),s.invoke(w)):(p!==P&&p.invoke("destroy"),s.initialize())}),b!==P?b:this},T.fn.checkbox.settings={name:"Checkbox",namespace:"checkbox",silent:!1,debug:!1,verbose:!0,performance:!0,uncheckable:"auto",fireOnInit:!1,onChange:function(){},beforeChecked:function(){},beforeUnchecked:function(){},beforeDeterminate:function(){},beforeIndeterminate:function(){},onChecked:function(){},onUnchecked:function(){},onDeterminate:function(){},onIndeterminate:function(){},onEnable:function(){},onDisable:function(){},onEnabled:function(){},onDisabled:function(){},className:{checked:"checked",indeterminate:"indeterminate",disabled:"disabled",hidden:"hidden",radio:"radio",readOnly:"read-only"},error:{method:"The method you called is not defined"},selector:{checkbox:".ui.checkbox",label:"label, .box",input:'input[type="checkbox"], input[type="radio"]',link:"a[href]"}}}(jQuery,window,document),function(S,e,k,T){"use strict";e=void 0!==e&&e.Math==Math?e:"undefined"!=typeof self&&self.Math==Math?self:Function("return this")(),S.fn.dimmer=function(p){var h,v=S(this),b=(new Date).getTime(),y=[],x=p,C="string"==typeof x,w=[].slice.call(arguments,1);return v.each(function(){var a,t,s,r=S.isPlainObject(p)?S.extend(!0,{},S.fn.dimmer.settings,p):S.extend({},S.fn.dimmer.settings),n=r.selector,e=r.namespace,i=r.className,l=r.error,o="."+e,c="module-"+e,u=v.selector||"",d="ontouchstart"in k.documentElement?"touchstart":"click",f=S(this),m=this,g=f.data(c);(s={preinitialize:function(){a=s.is.dimmer()?(t=f.parent(),f):(t=f,s.has.dimmer()?r.dimmerName?t.find(n.dimmer).filter("."+r.dimmerName):t.find(n.dimmer):s.create())},initialize:function(){s.debug("Initializing dimmer",r),s.bind.events(),s.set.dimmable(),s.instantiate()},instantiate:function(){s.verbose("Storing instance of module",s),g=s,f.data(c,g)},destroy:function(){s.verbose("Destroying previous module",a),s.unbind.events(),s.remove.variation(),t.off(o)},bind:{events:function(){"hover"==r.on?t.on("mouseenter"+o,s.show).on("mouseleave"+o,s.hide):"click"==r.on&&t.on(d+o,s.toggle),s.is.page()&&(s.debug("Setting as a page dimmer",t),s.set.pageDimmer()),s.is.closable()&&(s.verbose("Adding dimmer close event",a),t.on(d+o,n.dimmer,s.event.click))}},unbind:{events:function(){f.removeData(c),t.off(o)}},event:{click:function(e){s.verbose("Determining if event occured on dimmer",e),(0===a.find(e.target).length||S(e.target).is(n.content))&&(s.hide(),e.stopImmediatePropagation())}},addContent:function(e){var t=S(e);s.debug("Add content to dimmer",t),t.parent()[0]!==a[0]&&t.detach().appendTo(a)},create:function(){var e=S(r.template.dimmer());return r.dimmerName&&(s.debug("Creating named dimmer",r.dimmerName),e.addClass(r.dimmerName)),e.appendTo(t),e},show:function(e){e=S.isFunction(e)?e:function(){},s.debug("Showing dimmer",a,r),s.set.variation(),s.is.dimmed()&&!s.is.animating()||!s.is.enabled()?s.debug("Dimmer is already shown or disabled"):(s.animate.show(e),r.onShow.call(m),r.onChange.call(m))},hide:function(e){e=S.isFunction(e)?e:function(){},s.is.dimmed()||s.is.animating()?(s.debug("Hiding dimmer",a),s.animate.hide(e),r.onHide.call(m),r.onChange.call(m)):s.debug("Dimmer is not visible")},toggle:function(){s.verbose("Toggling dimmer visibility",a),s.is.dimmed()?s.hide():s.show()},animate:{show:function(e){e=S.isFunction(e)?e:function(){},r.useCSS&&S.fn.transition!==T&&a.transition("is supported")?(r.useFlex?(s.debug("Using flex dimmer"),s.remove.legacy()):(s.debug("Using legacy non-flex dimmer"),s.set.legacy()),"auto"!==r.opacity&&s.set.opacity(),a.transition({displayType:r.useFlex?"flex":"block",animation:r.transition+" in",queue:!1,duration:s.get.duration(),useFailSafe:!0,onStart:function(){s.set.dimmed()},onComplete:function(){s.set.active(),e()}})):(s.verbose("Showing dimmer animation with javascript"),s.set.dimmed(),"auto"==r.opacity&&(r.opacity=.8),a.stop().css({opacity:0,width:"100%",height:"100%"}).fadeTo(s.get.duration(),r.opacity,function(){a.removeAttr("style"),s.set.active(),e()}))},hide:function(e){e=S.isFunction(e)?e:function(){},r.useCSS&&S.fn.transition!==T&&a.transition("is supported")?(s.verbose("Hiding dimmer with css"),a.transition({displayType:r.useFlex?"flex":"block",animation:r.transition+" out",queue:!1,duration:s.get.duration(),useFailSafe:!0,onStart:function(){s.remove.dimmed()},onComplete:function(){s.remove.variation(),s.remove.active(),e()}})):(s.verbose("Hiding dimmer with javascript"),s.remove.dimmed(),a.stop().fadeOut(s.get.duration(),function(){s.remove.active(),a.removeAttr("style"),e()}))}},get:{dimmer:function(){return a},duration:function(){return"object"==typeof r.duration?s.is.active()?r.duration.hide:r.duration.show:r.duration}},has:{dimmer:function(){return r.dimmerName?0<f.find(n.dimmer).filter("."+r.dimmerName).length:0<f.find(n.dimmer).length}},is:{active:function(){return a.hasClass(i.active)},animating:function(){return a.is(":animated")||a.hasClass(i.animating)},closable:function(){return"auto"==r.closable?"hover"!=r.on:r.closable},dimmer:function(){return f.hasClass(i.dimmer)},dimmable:function(){return f.hasClass(i.dimmable)},dimmed:function(){return t.hasClass(i.dimmed)},disabled:function(){return t.hasClass(i.disabled)},enabled:function(){return!s.is.disabled()},page:function(){return t.is("body")},pageDimmer:function(){return a.hasClass(i.pageDimmer)}},can:{show:function(){return!a.hasClass(i.disabled)}},set:{opacity:function(e){var t=a.css("background-color"),n=t.split(","),i=n&&3==n.length,o=n&&4==n.length;e=0===r.opacity?0:r.opacity||e,t=i||o?(n[3]=e+")",n.join(",")):"rgba(0, 0, 0, "+e+")",s.debug("Setting opacity to",e),a.css("background-color",t)},legacy:function(){a.addClass(i.legacy)},active:function(){a.addClass(i.active)},dimmable:function(){t.addClass(i.dimmable)},dimmed:function(){t.addClass(i.dimmed)},pageDimmer:function(){a.addClass(i.pageDimmer)},disabled:function(){a.addClass(i.disabled)},variation:function(e){(e=e||r.variation)&&a.addClass(e)}},remove:{active:function(){a.removeClass(i.active)},legacy:function(){a.removeClass(i.legacy)},dimmed:function(){t.removeClass(i.dimmed)},disabled:function(){a.removeClass(i.disabled)},variation:function(e){(e=e||r.variation)&&a.removeClass(e)}},setting:function(e,t){if(s.debug("Changing setting",e,t),S.isPlainObject(e))S.extend(!0,r,e);else{if(t===T)return r[e];S.isPlainObject(r[e])?S.extend(!0,r[e],t):r[e]=t}},internal:function(e,t){if(S.isPlainObject(e))S.extend(!0,s,e);else{if(t===T)return s[e];s[e]=t}},debug:function(){!r.silent&&r.debug&&(r.performance?s.performance.log(arguments):(s.debug=Function.prototype.bind.call(console.info,console,r.name+":"),s.debug.apply(console,arguments)))},verbose:function(){!r.silent&&r.verbose&&r.debug&&(r.performance?s.performance.log(arguments):(s.verbose=Function.prototype.bind.call(console.info,console,r.name+":"),s.verbose.apply(console,arguments)))},error:function(){r.silent||(s.error=Function.prototype.bind.call(console.error,console,r.name+":"),s.error.apply(console,arguments))},performance:{log:function(e){var t,n;r.performance&&(n=(t=(new Date).getTime())-(b||t),b=t,y.push({Name:e[0],Arguments:[].slice.call(e,1)||"",Element:m,"Execution Time":n})),clearTimeout(s.performance.timer),s.performance.timer=setTimeout(s.performance.display,500)},display:function(){var e=r.name+":",n=0;b=!1,clearTimeout(s.performance.timer),S.each(y,function(e,t){n+=t["Execution Time"]}),e+=" "+n+"ms",u&&(e+=" '"+u+"'"),1<v.length&&(e+=" ("+v.length+")"),(console.group!==T||console.table!==T)&&0<y.length&&(console.groupCollapsed(e),console.table?console.table(y):S.each(y,function(e,t){console.log(t.Name+": "+t["Execution Time"]+"ms")}),console.groupEnd()),y=[]}},invoke:function(i,e,t){var o,a,n,r=g;return e=e||w,t=m||t,"string"==typeof i&&r!==T&&(i=i.split(/[\. ]/),o=i.length-1,S.each(i,function(e,t){var n=e!=o?t+i[e+1].charAt(0).toUpperCase()+i[e+1].slice(1):i;if(S.isPlainObject(r[n])&&e!=o)r=r[n];else{if(r[n]!==T)return a=r[n],!1;if(!S.isPlainObject(r[t])||e==o)return r[t]!==T?a=r[t]:s.error(l.method,i),!1;r=r[t]}})),S.isFunction(a)?n=a.apply(t,e):a!==T&&(n=a),S.isArray(h)?h.push(n):h!==T?h=[h,n]:n!==T&&(h=n),a}}).preinitialize(),C?(g===T&&s.initialize(),s.invoke(x)):(g!==T&&g.invoke("destroy"),s.initialize())}),h!==T?h:this},S.fn.dimmer.settings={name:"Dimmer",namespace:"dimmer",silent:!1,debug:!1,verbose:!1,performance:!0,useFlex:!0,dimmerName:!1,variation:!1,closable:"auto",useCSS:!0,transition:"fade",on:!1,opacity:"auto",duration:{show:500,hide:500},onChange:function(){},onShow:function(){},onHide:function(){},error:{method:"The method you called is not defined."},className:{active:"active",animating:"animating",dimmable:"dimmable",dimmed:"dimmed",dimmer:"dimmer",disabled:"disabled",hide:"hide",legacy:"legacy",pageDimmer:"page",show:"show"},selector:{dimmer:"> .ui.dimmer",content:".ui.dimmer > .content, .ui.dimmer > .content > .center"},template:{dimmer:function(){return S("<div />").attr("class","ui dimmer")}}}}(jQuery,window,document),function(Y,Z,K,J){"use strict";Z=void 0!==Z&&Z.Math==Math?Z:"undefined"!=typeof self&&self.Math==Math?self:Function("return this")(),Y.fn.dropdown=function(M){var L,V=Y(this),N=Y(K),H=V.selector||"",U="ontouchstart"in K.documentElement,W=(new Date).getTime(),B=[],Q=M,X="string"==typeof Q,$=[].slice.call(arguments,1);return V.each(function(n){var e,t,i,o,a,r,s,g,p=Y.isPlainObject(M)?Y.extend(!0,{},Y.fn.dropdown.settings,M):Y.extend({},Y.fn.dropdown.settings),h=p.className,c=p.message,l=p.fields,v=p.keys,b=p.metadata,u=p.namespace,d=p.regExp,y=p.selector,f=p.error,m=p.templates,x="."+u,C="module-"+u,w=Y(this),S=Y(p.context),k=w.find(y.text),T=w.find(y.search),A=w.find(y.sizer),R=w.find(y.input),P=w.find(y.icon),E=0<w.prev().find(y.text).length?w.prev().find(y.text):w.prev(),F=w.children(y.menu),O=F.find(y.item),D=!1,q=!1,j=!1,z=this,I=w.data(C);g={initialize:function(){g.debug("Initializing dropdown",p),g.is.alreadySetup()?g.setup.reference():(g.setup.layout(),p.values&&g.change.values(p.values),g.refreshData(),g.save.defaults(),g.restore.selected(),g.create.id(),g.bind.events(),g.observeChanges(),g.instantiate())},instantiate:function(){g.verbose("Storing instance of dropdown",g),I=g,w.data(C,g)},destroy:function(){g.verbose("Destroying previous dropdown",w),g.remove.tabbable(),w.off(x).removeData(C),F.off(x),N.off(o),g.disconnect.menuObserver(),g.disconnect.selectObserver()},observeChanges:function(){"MutationObserver"in Z&&(r=new MutationObserver(g.event.select.mutation),s=new MutationObserver(g.event.menu.mutation),g.debug("Setting up mutation observer",r,s),g.observe.select(),g.observe.menu())},disconnect:{menuObserver:function(){s&&s.disconnect()},selectObserver:function(){r&&r.disconnect()}},observe:{select:function(){g.has.input()&&r.observe(w[0],{childList:!0,subtree:!0})},menu:function(){g.has.menu()&&s.observe(F[0],{childList:!0,subtree:!0})}},create:{id:function(){a=(Math.random().toString(16)+"000000000").substr(2,8),o="."+a,g.verbose("Creating unique id for element",a)},userChoice:function(e){var n,i,o;return!!(e=e||g.get.userValues())&&(e=Y.isArray(e)?e:[e],Y.each(e,function(e,t){!1===g.get.item(t)&&(o=p.templates.addition(g.add.variables(c.addResult,t)),i=Y("<div />").html(o).attr("data-"+b.value,t).attr("data-"+b.text,t).addClass(h.addition).addClass(h.item),p.hideAdditions&&i.addClass(h.hidden),n=n===J?i:n.add(i),g.verbose("Creating user choices for value",t,i))}),n)},userLabels:function(e){var t=g.get.userValues();t&&(g.debug("Adding user labels",t),Y.each(t,function(e,t){g.verbose("Adding custom user value"),g.add.label(t,t)}))},menu:function(){F=Y("<div />").addClass(h.menu).appendTo(w)},sizer:function(){A=Y("<span />").addClass(h.sizer).insertAfter(T)}},search:function(e){e=e!==J?e:g.get.query(),g.verbose("Searching for query",e),g.has.minCharacters(e)?g.filter(e):g.hide()},select:{firstUnfiltered:function(){g.verbose("Selecting first non-filtered element"),g.remove.selectedItem(),O.not(y.unselectable).not(y.addition+y.hidden).eq(0).addClass(h.selected)},nextAvailable:function(e){var t=(e=e.eq(0)).nextAll(y.item).not(y.unselectable).eq(0),n=e.prevAll(y.item).not(y.unselectable).eq(0);0<t.length?(g.verbose("Moving selection to",t),t.addClass(h.selected)):(g.verbose("Moving selection to",n),n.addClass(h.selected))}},setup:{api:function(){var e={debug:p.debug,urlData:{value:g.get.value(),query:g.get.query()},on:!1};g.verbose("First request, initializing API"),w.api(e)},layout:function(){w.is("select")&&(g.setup.select(),g.setup.returnedObject()),g.has.menu()||g.create.menu(),g.is.search()&&!g.has.search()&&(g.verbose("Adding search input"),T=Y("<input />").addClass(h.search).prop("autocomplete","off").insertBefore(k)),g.is.multiple()&&g.is.searchSelection()&&!g.has.sizer()&&g.create.sizer(),p.allowTab&&g.set.tabbable()},select:function(){var e=g.get.selectValues();g.debug("Dropdown initialized on a select",e),w.is("select")&&(R=w),0<R.parent(y.dropdown).length?(g.debug("UI dropdown already exists. Creating dropdown menu only"),w=R.closest(y.dropdown),g.has.menu()||g.create.menu(),F=w.children(y.menu),g.setup.menu(e)):(g.debug("Creating entire dropdown from select"),w=Y("<div />").attr("class",R.attr("class")).addClass(h.selection).addClass(h.dropdown).html(m.dropdown(e)).insertBefore(R),R.hasClass(h.multiple)&&!1===R.prop("multiple")&&(g.error(f.missingMultiple),R.prop("multiple",!0)),R.is("[multiple]")&&g.set.multiple(),R.prop("disabled")&&(g.debug("Disabling dropdown"),w.addClass(h.disabled)),R.removeAttr("class").detach().prependTo(w)),g.refresh()},menu:function(e){F.html(m.menu(e,l)),O=F.find(y.item)},reference:function(){g.debug("Dropdown behavior was called on select, replacing with closest dropdown"),w=w.parent(y.dropdown),I=w.data(C),z=w.get(0),g.refresh(),g.setup.returnedObject()},returnedObject:function(){var e=V.slice(0,n),t=V.slice(n+1);V=e.add(w).add(t)}},refresh:function(){g.refreshSelectors(),g.refreshData()},refreshItems:function(){O=F.find(y.item)},refreshSelectors:function(){g.verbose("Refreshing selector cache"),k=w.find(y.text),T=w.find(y.search),R=w.find(y.input),P=w.find(y.icon),E=0<w.prev().find(y.text).length?w.prev().find(y.text):w.prev(),F=w.children(y.menu),O=F.find(y.item)},refreshData:function(){g.verbose("Refreshing cached metadata"),O.removeData(b.text).removeData(b.value)},clearData:function(){g.verbose("Clearing metadata"),O.removeData(b.text).removeData(b.value),w.removeData(b.defaultText).removeData(b.defaultValue).removeData(b.placeholderText)},toggle:function(){g.verbose("Toggling menu visibility"),g.is.active()?g.hide():g.show()},show:function(e){if(e=Y.isFunction(e)?e:function(){},!g.can.show()&&g.is.remote()&&(g.debug("No API results retrieved, searching before show"),g.queryRemote(g.get.query(),g.show)),g.can.show()&&!g.is.active()){if(g.debug("Showing dropdown"),!g.has.message()||g.has.maxSelections()||g.has.allResultsFiltered()||g.remove.message(),g.is.allFiltered())return!0;!1!==p.onShow.call(z)&&g.animate.show(function(){g.can.click()&&g.bind.intent(),g.has.menuSearch()&&g.focusSearch(),g.set.visible(),e.call(z)})}},hide:function(e){e=Y.isFunction(e)?e:function(){},g.is.active()&&!g.is.animatingOutward()&&(g.debug("Hiding dropdown"),!1!==p.onHide.call(z)&&g.animate.hide(function(){g.remove.visible(),e.call(z)}))},hideOthers:function(){g.verbose("Finding other dropdowns to hide"),V.not(w).has(y.menu+"."+h.visible).dropdown("hide")},hideMenu:function(){g.verbose("Hiding menu  instantaneously"),g.remove.active(),g.remove.visible(),F.transition("hide")},hideSubMenus:function(){var e=F.children(y.item).find(y.menu);g.verbose("Hiding sub menus",e),e.transition("hide")},bind:{events:function(){U&&g.bind.touchEvents(),g.bind.keyboardEvents(),g.bind.inputEvents(),g.bind.mouseEvents()},touchEvents:function(){g.debug("Touch device detected binding additional touch events"),g.is.searchSelection()||g.is.single()&&w.on("touchstart"+x,g.event.test.toggle),F.on("touchstart"+x,y.item,g.event.item.mouseenter)},keyboardEvents:function(){g.verbose("Binding keyboard events"),w.on("keydown"+x,g.event.keydown),g.has.search()&&w.on(g.get.inputEvent()+x,y.search,g.event.input),g.is.multiple()&&N.on("keydown"+o,g.event.document.keydown)},inputEvents:function(){g.verbose("Binding input change events"),w.on("change"+x,y.input,g.event.change)},mouseEvents:function(){g.verbose("Binding mouse events"),g.is.multiple()&&w.on("click"+x,y.label,g.event.label.click).on("click"+x,y.remove,g.event.remove.click),g.is.searchSelection()?(w.on("mousedown"+x,g.event.mousedown).on("mouseup"+x,g.event.mouseup).on("mousedown"+x,y.menu,g.event.menu.mousedown).on("mouseup"+x,y.menu,g.event.menu.mouseup).on("click"+x,y.icon,g.event.icon.click).on("focus"+x,y.search,g.event.search.focus).on("click"+x,y.search,g.event.search.focus).on("blur"+x,y.search,g.event.search.blur).on("click"+x,y.text,g.event.text.focus),g.is.multiple()&&w.on("click"+x,g.event.click)):("click"==p.on?w.on("click"+x,g.event.test.toggle):"hover"==p.on?w.on("mouseenter"+x,g.delay.show).on("mouseleave"+x,g.delay.hide):w.on(p.on+x,g.toggle),w.on("click"+x,y.icon,g.event.icon.click).on("mousedown"+x,g.event.mousedown).on("mouseup"+x,g.event.mouseup).on("focus"+x,g.event.focus),g.has.menuSearch()?w.on("blur"+x,y.search,g.event.search.blur):w.on("blur"+x,g.event.blur)),F.on("mouseenter"+x,y.item,g.event.item.mouseenter).on("mouseleave"+x,y.item,g.event.item.mouseleave).on("click"+x,y.item,g.event.item.click)},intent:function(){g.verbose("Binding hide intent event to document"),U&&N.on("touchstart"+o,g.event.test.touch).on("touchmove"+o,g.event.test.touch),N.on("click"+o,g.event.test.hide)}},unbind:{intent:function(){g.verbose("Removing hide intent event from document"),U&&N.off("touchstart"+o).off("touchmove"+o),N.off("click"+o)}},filter:function(e){var t=e!==J?e:g.get.query(),n=function(){g.is.multiple()&&g.filterActive(),(e||!e&&0==g.get.activeItem().length)&&g.select.firstUnfiltered(),g.has.allResultsFiltered()?p.onNoResults.call(z,t)?p.allowAdditions?p.hideAdditions&&(g.verbose("User addition with no menu, setting empty style"),g.set.empty(),g.hideMenu()):(g.verbose("All items filtered, showing message",t),g.add.message(c.noResults)):(g.verbose("All items filtered, hiding dropdown",t),g.hideMenu()):(g.remove.empty(),g.remove.message()),p.allowAdditions&&g.add.userSuggestion(e),g.is.searchSelection()&&g.can.show()&&g.is.focusedOnSearch()&&g.show()};p.useLabels&&g.has.maxSelections()||(p.apiSettings?g.can.useAPI()?g.queryRemote(t,function(){p.filterRemoteData&&g.filterItems(t),n()}):g.error(f.noAPI):(g.filterItems(t),n()))},queryRemote:function(e,n){var t={errorDuration:!1,cache:"local",throttle:p.throttle,urlData:{query:e},onError:function(){g.add.message(c.serverError),n()},onFailure:function(){g.add.message(c.serverError),n()},onSuccess:function(e){var t=e[l.remoteValues];Y.isArray(t)&&0<t.length?(g.remove.message(),g.setup.menu({values:e[l.remoteValues]})):g.add.message(c.noResults),n()}};w.api("get request")||g.setup.api(),t=Y.extend(!0,{},t,p.apiSettings),w.api("setting",t).api("query")},filterItems:function(e){var i=e!==J?e:g.get.query(),o=null,t=g.escape.string(i),a=new RegExp("^"+t,"igm");g.has.query()&&(o=[],g.verbose("Searching for matching values",i),O.each(function(){var e,t,n=Y(this);if("both"==p.match||"text"==p.match){if(-1!==(e=String(g.get.choiceText(n,!1))).search(a))return o.push(this),!0;if("exact"===p.fullTextSearch&&g.exactSearch(i,e))return o.push(this),!0;if(!0===p.fullTextSearch&&g.fuzzySearch(i,e))return o.push(this),!0}if("both"==p.match||"value"==p.match){if(-1!==(t=String(g.get.choiceValue(n,e))).search(a))return o.push(this),!0;if("exact"===p.fullTextSearch&&g.exactSearch(i,t))return o.push(this),!0;if(!0===p.fullTextSearch&&g.fuzzySearch(i,t))return o.push(this),!0}})),g.debug("Showing only matched items",i),g.remove.filteredItem(),o&&O.not(o).addClass(h.filtered)},fuzzySearch:function(e,t){var n=t.length,i=e.length;if(e=e.toLowerCase(),t=t.toLowerCase(),n<i)return!1;if(i===n)return e===t;e:for(var o=0,a=0;o<i;o++){for(var r=e.charCodeAt(o);a<n;)if(t.charCodeAt(a++)===r)continue e;return!1}return!0},exactSearch:function(e,t){return e=e.toLowerCase(),-1<(t=t.toLowerCase()).indexOf(e)},filterActive:function(){p.useLabels&&O.filter("."+h.active).addClass(h.filtered)},focusSearch:function(e){g.has.search()&&!g.is.focusedOnSearch()&&(e?(w.off("focus"+x,y.search),T.focus(),w.on("focus"+x,y.search,g.event.search.focus)):T.focus())},forceSelection:function(){var e=O.not(h.filtered).filter("."+h.selected).eq(0),t=O.not(h.filtered).filter("."+h.active).eq(0),n=0<e.length?e:t;if(0<n.length&&!g.is.multiple())return g.debug("Forcing partial selection to selected item",n),void g.event.item.click.call(n,{},!0);p.allowAdditions&&g.set.selected(g.get.query()),g.remove.searchTerm()},change:{values:function(e){p.allowAdditions||g.clear(),g.debug("Creating dropdown with specified values",e),g.setup.menu({values:e}),Y.each(e,function(e,t){if(1==t.selected)return g.debug("Setting initial selection to",t.value),g.set.selected(t.value),!0})}},event:{change:function(){j||(g.debug("Input changed, updating selection"),g.set.selected())},focus:function(){p.showOnFocus&&!D&&g.is.hidden()&&!t&&g.show()},blur:function(e){t=K.activeElement===this,D||t||(g.remove.activeLabel(),g.hide())},mousedown:function(){g.is.searchSelection()?i=!0:D=!0},mouseup:function(){g.is.searchSelection()?i=!1:D=!1},click:function(e){Y(e.target).is(w)&&(g.is.focusedOnSearch()?g.show():g.focusSearch())},search:{focus:function(){D=!0,g.is.multiple()&&g.remove.activeLabel(),p.showOnFocus&&g.search()},blur:function(e){t=K.activeElement===this,g.is.searchSelection()&&!i&&(q||t||(p.forceSelection&&g.forceSelection(),g.hide())),i=!1}},icon:{click:function(e){P.hasClass(h.clear)?g.clear():g.can.click()&&g.toggle()}},text:{focus:function(e){D=!0,g.focusSearch()}},input:function(e){(g.is.multiple()||g.is.searchSelection())&&g.set.filtered(),clearTimeout(g.timer),g.timer=setTimeout(g.search,p.delay.search)},label:{click:function(e){var t=Y(this),n=w.find(y.label),i=n.filter("."+h.active),o=t.nextAll("."+h.active),a=t.prevAll("."+h.active),r=0<o.length?t.nextUntil(o).add(i).add(t):t.prevUntil(a).add(i).add(t);e.shiftKey?(i.removeClass(h.active),r.addClass(h.active)):e.ctrlKey?t.toggleClass(h.active):(i.removeClass(h.active),t.addClass(h.active)),p.onLabelSelect.apply(this,n.filter("."+h.active))}},remove:{click:function(){var e=Y(this).parent();e.hasClass(h.active)?g.remove.activeLabels():g.remove.activeLabels(e)}},test:{toggle:function(e){var t=g.is.multiple()?g.show:g.toggle;g.is.bubbledLabelClick(e)||g.is.bubbledIconClick(e)||g.determine.eventOnElement(e,t)&&e.preventDefault()},touch:function(e){g.determine.eventOnElement(e,function(){"touchstart"==e.type?g.timer=setTimeout(function(){g.hide()},p.delay.touch):"touchmove"==e.type&&clearTimeout(g.timer)}),e.stopPropagation()},hide:function(e){g.determine.eventInModule(e,g.hide)}},select:{mutation:function(e){g.debug("<select> modified, recreating menu");var n=!1;Y.each(e,function(e,t){if(Y(t.target).is("select")||Y(t.addedNodes).is("select"))return n=!0}),n&&(g.disconnect.selectObserver(),g.refresh(),g.setup.select(),g.set.selected(),g.observe.select())}},menu:{mutation:function(e){var t=e[0],n=t.addedNodes?Y(t.addedNodes[0]):Y(!1),i=t.removedNodes?Y(t.removedNodes[0]):Y(!1),o=n.add(i),a=o.is(y.addition)||0<o.closest(y.addition).length,r=o.is(y.message)||0<o.closest(y.message).length;a||r?(g.debug("Updating item selector cache"),g.refreshItems()):(g.debug("Menu modified, updating selector cache"),g.refresh())},mousedown:function(){q=!0},mouseup:function(){q=!1}},item:{mouseenter:function(e){var t=Y(e.target),n=Y(this),i=n.children(y.menu),o=n.siblings(y.item).children(y.menu),a=0<i.length;!(0<i.find(t).length)&&a&&(clearTimeout(g.itemTimer),g.itemTimer=setTimeout(function(){g.verbose("Showing sub-menu",i),Y.each(o,function(){g.animate.hide(!1,Y(this))}),g.animate.show(!1,i)},p.delay.show),e.preventDefault())},mouseleave:function(e){var t=Y(this).children(y.menu);0<t.length&&(clearTimeout(g.itemTimer),g.itemTimer=setTimeout(function(){g.verbose("Hiding sub-menu",t),g.animate.hide(!1,t)},p.delay.hide))},click:function(e,t){var n=Y(this),i=Y(e?e.target:""),o=n.find(y.menu),a=g.get.choiceText(n),r=g.get.choiceValue(n,a),s=0<o.length,l=0<o.find(i).length;g.has.menuSearch()&&Y(K.activeElement).blur(),l||s&&!p.allowCategorySelection||(g.is.searchSelection()&&(p.allowAdditions&&g.remove.userAddition(),g.remove.searchTerm(),g.is.focusedOnSearch()||1==t||g.focusSearch(!0)),p.useLabels||(g.remove.filteredItem(),g.set.scrollPosition(n)),g.determine.selectAction.call(this,a,r))}},document:{keydown:function(e){var t=e.which;if(g.is.inObject(t,v)){var n=w.find(y.label),i=n.filter("."+h.active),o=(i.data(b.value),n.index(i)),a=n.length,r=0<i.length,s=1<i.length,l=0===o,c=o+1==a,u=g.is.searchSelection(),d=g.is.focusedOnSearch(),f=g.is.focused(),m=d&&0===g.get.caretPosition();if(u&&!r&&!d)return;t==v.leftArrow?!f&&!m||r?r&&(e.shiftKey?g.verbose("Adding previous label to selection"):(g.verbose("Selecting previous label"),n.removeClass(h.active)),l&&!s?i.addClass(h.active):i.prev(y.siblingLabel).addClass(h.active).end(),e.preventDefault()):(g.verbose("Selecting previous label"),n.last().addClass(h.active)):t==v.rightArrow?(f&&!r&&n.first().addClass(h.active),r&&(e.shiftKey?g.verbose("Adding next label to selection"):(g.verbose("Selecting next label"),n.removeClass(h.active)),c?u?d?n.removeClass(h.active):g.focusSearch():s?i.next(y.siblingLabel).addClass(h.active):i.addClass(h.active):i.next(y.siblingLabel).addClass(h.active),e.preventDefault())):t==v.deleteKey||t==v.backspace?r?(g.verbose("Removing active labels"),c&&u&&!d&&g.focusSearch(),i.last().next(y.siblingLabel).addClass(h.active),g.remove.activeLabels(i),e.preventDefault()):m&&!r&&t==v.backspace&&(g.verbose("Removing last label on input backspace"),i=n.last().addClass(h.active),g.remove.activeLabels(i)):i.removeClass(h.active)}}},keydown:function(e){var t=e.which;if(g.is.inObject(t,v)){var n,i=O.not(y.unselectable).filter("."+h.selected).eq(0),o=F.children("."+h.active).eq(0),a=0<i.length?i:o,r=0<a.length?a.siblings(":not(."+h.filtered+")").addBack():F.children(":not(."+h.filtered+")"),s=a.children(y.menu),l=a.closest(y.menu),c=l.hasClass(h.visible)||l.hasClass(h.animating)||0<l.parent(y.menu).length,u=0<s.length,d=0<a.length,f=0<a.not(y.unselectable).length,m=t==v.delimiter&&p.allowAdditions&&g.is.multiple();if(p.allowAdditions&&p.hideAdditions&&(t==v.enter||m)&&f&&(g.verbose("Selecting item from keyboard shortcut",a),g.event.item.click.call(a,e),g.is.searchSelection()&&g.remove.searchTerm()),g.is.visible()){if((t==v.enter||m)&&(t==v.enter&&d&&u&&!p.allowCategorySelection?(g.verbose("Pressed enter on unselectable category, opening sub menu"),t=v.rightArrow):f&&(g.verbose("Selecting item from keyboard shortcut",a),g.event.item.click.call(a,e),g.is.searchSelection()&&g.remove.searchTerm()),e.preventDefault()),d&&(t==v.leftArrow&&l[0]!==F[0]&&(g.verbose("Left key pressed, closing sub-menu"),g.animate.hide(!1,l),a.removeClass(h.selected),l.closest(y.item).addClass(h.selected),e.preventDefault()),t==v.rightArrow&&u&&(g.verbose("Right key pressed, opening sub-menu"),g.animate.show(!1,s),a.removeClass(h.selected),s.find(y.item).eq(0).addClass(h.selected),e.preventDefault())),t==v.upArrow){if(n=d&&c?a.prevAll(y.item+":not("+y.unselectable+")").eq(0):O.eq(0),r.index(n)<0)return g.verbose("Up key pressed but reached top of current menu"),void e.preventDefault();g.verbose("Up key pressed, changing active item"),a.removeClass(h.selected),n.addClass(h.selected),g.set.scrollPosition(n),p.selectOnKeydown&&g.is.single()&&g.set.selectedItem(n),e.preventDefault()}if(t==v.downArrow){if(0===(n=d&&c?n=a.nextAll(y.item+":not("+y.unselectable+")").eq(0):O.eq(0)).length)return g.verbose("Down key pressed but reached bottom of current menu"),void e.preventDefault();g.verbose("Down key pressed, changing active item"),O.removeClass(h.selected),n.addClass(h.selected),g.set.scrollPosition(n),p.selectOnKeydown&&g.is.single()&&g.set.selectedItem(n),e.preventDefault()}t==v.pageUp&&(g.scrollPage("up"),e.preventDefault()),t==v.pageDown&&(g.scrollPage("down"),e.preventDefault()),t==v.escape&&(g.verbose("Escape key pressed, closing dropdown"),g.hide())}else m&&e.preventDefault(),t!=v.downArrow||g.is.visible()||(g.verbose("Down key pressed, showing dropdown"),g.show(),e.preventDefault())}else g.has.search()||g.set.selectedLetter(String.fromCharCode(t))}},trigger:{change:function(){var e=K.createEvent("HTMLEvents"),t=R[0];t&&(g.verbose("Triggering native change event"),e.initEvent("change",!0,!1),t.dispatchEvent(e))}},determine:{selectAction:function(e,t){g.verbose("Determining action",p.action),Y.isFunction(g.action[p.action])?(g.verbose("Triggering preset action",p.action,e,t),g.action[p.action].call(z,e,t,this)):Y.isFunction(p.action)?(g.verbose("Triggering user action",p.action,e,t),p.action.call(z,e,t,this)):g.error(f.action,p.action)},eventInModule:function(e,t){var n=Y(e.target),i=0<n.closest(K.documentElement).length,o=0<n.closest(w).length;return t=Y.isFunction(t)?t:function(){},i&&!o?(g.verbose("Triggering event",t),t(),!0):(g.verbose("Event occurred in dropdown, canceling callback"),!1)},eventOnElement:function(e,t){var n=Y(e.target),i=n.closest(y.siblingLabel),o=K.body.contains(e.target),a=0===w.find(i).length,r=0===n.closest(F).length;return t=Y.isFunction(t)?t:function(){},o&&a&&r?(g.verbose("Triggering event",t),t(),!0):(g.verbose("Event occurred in dropdown menu, canceling callback"),!1)}},action:{nothing:function(){},activate:function(e,t,n){if(t=t!==J?t:e,g.can.activate(Y(n))){if(g.set.selected(t,Y(n)),g.is.multiple()&&!g.is.allFiltered())return;g.hideAndClear()}},select:function(e,t,n){if(t=t!==J?t:e,g.can.activate(Y(n))){if(g.set.value(t,e,Y(n)),g.is.multiple()&&!g.is.allFiltered())return;g.hideAndClear()}},combo:function(e,t,n){t=t!==J?t:e,g.set.selected(t,Y(n)),g.hideAndClear()},hide:function(e,t,n){g.set.value(t,e,Y(n)),g.hideAndClear()}},get:{id:function(){return a},defaultText:function(){return w.data(b.defaultText)},defaultValue:function(){return w.data(b.defaultValue)},placeholderText:function(){return"auto"!=p.placeholder&&"string"==typeof p.placeholder?p.placeholder:w.data(b.placeholderText)||""},text:function(){return k.text()},query:function(){return Y.trim(T.val())},searchWidth:function(e){return e=e!==J?e:T.val(),A.text(e),Math.ceil(A.width()+1)},selectionCount:function(){var e=g.get.values();return g.is.multiple()?Y.isArray(e)?e.length:0:""!==g.get.value()?1:0},transition:function(e){return"auto"==p.transition?g.is.upward(e)?"slide up":"slide down":p.transition},userValues:function(){var e=g.get.values();return!!e&&(e=Y.isArray(e)?e:[e],Y.grep(e,function(e){return!1===g.get.item(e)}))},uniqueArray:function(n){return Y.grep(n,function(e,t){return Y.inArray(e,n)===t})},caretPosition:function(){var e,t,n=T.get(0);return"selectionStart"in n?n.selectionStart:K.selection?(n.focus(),t=(e=K.selection.createRange()).text.length,e.moveStart("character",-n.value.length),e.text.length-t):void 0},value:function(){var e=0<R.length?R.val():w.data(b.value),t=Y.isArray(e)&&1===e.length&&""===e[0];return e===J||t?"":e},values:function(){var e=g.get.value();return""===e?"":!g.has.selectInput()&&g.is.multiple()?"string"==typeof e?e.split(p.delimiter):"":e},remoteValues:function(){var e=g.get.values(),i=!1;return e&&("string"==typeof e&&(e=[e]),Y.each(e,function(e,t){var n=g.read.remoteData(t);g.verbose("Restoring value from session data",n,t),n&&(i||(i={}),i[t]=n)})),i},choiceText:function(e,t){if(t=t!==J?t:p.preserveHTML,e)return 0<e.find(y.menu).length&&(g.verbose("Retrieving text of element with sub-menu"),(e=e.clone()).find(y.menu).remove(),e.find(y.menuIcon).remove()),e.data(b.text)!==J?e.data(b.text):t?Y.trim(e.html()):Y.trim(e.text())},choiceValue:function(e,t){return t=t||g.get.choiceText(e),!!e&&(e.data(b.value)!==J?String(e.data(b.value)):"string"==typeof t?Y.trim(t.toLowerCase()):String(t))},inputEvent:function(){var e=T[0];return!!e&&(e.oninput!==J?"input":e.onpropertychange!==J?"propertychange":"keyup")},selectValues:function(){var o={values:[]};return w.find("option").each(function(){var e=Y(this),t=e.html(),n=e.attr("disabled"),i=e.attr("value")!==J?e.attr("value"):t;"auto"===p.placeholder&&""===i?o.placeholder=t:o.values.push({name:t,value:i,disabled:n})}),p.placeholder&&"auto"!==p.placeholder&&(g.debug("Setting placeholder value to",p.placeholder),o.placeholder=p.placeholder),p.sortSelect?(o.values.sort(function(e,t){return e.name>t.name?1:-1}),g.debug("Retrieved and sorted values from select",o)):g.debug("Retrieved values from select",o),o},activeItem:function(){return O.filter("."+h.active)},selectedItem:function(){var e=O.not(y.unselectable).filter("."+h.selected);return 0<e.length?e:O.eq(0)},itemWithAdditions:function(e){var t=g.get.item(e),n=g.create.userChoice(e);return n&&0<n.length&&(t=0<t.length?t.add(n):n),t},item:function(i,o){var e,a,r=!1;return i=i!==J?i:g.get.values()!==J?g.get.values():g.get.text(),e=a?0<i.length:i!==J&&null!==i,a=g.is.multiple()&&Y.isArray(i),o=""===i||0===i||(o||!1),e&&O.each(function(){var e=Y(this),t=g.get.choiceText(e),n=g.get.choiceValue(e,t);if(null!==n&&n!==J)if(a)-1===Y.inArray(String(n),i)&&-1===Y.inArray(t,i)||(r=r?r.add(e):e);else if(o){if(g.verbose("Ambiguous dropdown value using strict type check",e,i),n===i||t===i)return r=e,!0}else if(String(n)==String(i)||t==i)return g.verbose("Found select item by value",n,i),r=e,!0}),r}},check:{maxSelections:function(e){return!p.maxSelections||((e=e!==J?e:g.get.selectionCount())>=p.maxSelections?(g.debug("Maximum selection count reached"),p.useLabels&&(O.addClass(h.filtered),g.add.message(c.maxSelections)),!0):(g.verbose("No longer at maximum selection count"),g.remove.message(),g.remove.filteredItem(),g.is.searchSelection()&&g.filterItems(),!1))}},restore:{defaults:function(){g.clear(),g.restore.defaultText(),g.restore.defaultValue()},defaultText:function(){var e=g.get.defaultText();e===g.get.placeholderText?(g.debug("Restoring default placeholder text",e),g.set.placeholderText(e)):(g.debug("Restoring default text",e),g.set.text(e))},placeholderText:function(){g.set.placeholderText()},defaultValue:function(){var e=g.get.defaultValue();e!==J&&(g.debug("Restoring default value",e),""!==e?(g.set.value(e),g.set.selected()):(g.remove.activeItem(),g.remove.selectedItem()))},labels:function(){p.allowAdditions&&(p.useLabels||(g.error(f.labels),p.useLabels=!0),g.debug("Restoring selected values"),g.create.userLabels()),g.check.maxSelections()},selected:function(){g.restore.values(),g.is.multiple()?(g.debug("Restoring previously selected values and labels"),g.restore.labels()):g.debug("Restoring previously selected values")},values:function(){g.set.initialLoad(),p.apiSettings&&p.saveRemoteData&&g.get.remoteValues()?g.restore.remoteValues():g.set.selected(),g.remove.initialLoad()},remoteValues:function(){var e=g.get.remoteValues();g.debug("Recreating selected from session data",e),e&&(g.is.single()?Y.each(e,function(e,t){g.set.text(t)}):Y.each(e,function(e,t){g.add.label(e,t)}))}},read:{remoteData:function(e){var t;if(Z.Storage!==J)return(t=sessionStorage.getItem(e))!==J&&t;g.error(f.noStorage)}},save:{defaults:function(){g.save.defaultText(),g.save.placeholderText(),g.save.defaultValue()},defaultValue:function(){var e=g.get.value();g.verbose("Saving default value as",e),w.data(b.defaultValue,e)},defaultText:function(){var e=g.get.text();g.verbose("Saving default text as",e),w.data(b.defaultText,e)},placeholderText:function(){var e;!1!==p.placeholder&&k.hasClass(h.placeholder)&&(e=g.get.text(),g.verbose("Saving placeholder text as",e),w.data(b.placeholderText,e))},remoteData:function(e,t){Z.Storage!==J?(g.verbose("Saving remote data to session storage",t,e),sessionStorage.setItem(t,e)):g.error(f.noStorage)}},clear:function(){g.is.multiple()&&p.useLabels?g.remove.labels():(g.remove.activeItem(),g.remove.selectedItem()),g.set.placeholderText(),g.clearValue()},clearValue:function(){g.set.value("")},scrollPage:function(e,t){var n,i,o=t||g.get.selectedItem(),a=o.closest(y.menu),r=a.outerHeight(),s=a.scrollTop(),l=O.eq(0).outerHeight(),c=Math.floor(r/l),u=(a.prop("scrollHeight"),"up"==e?s-l*c:s+l*c),d=O.not(y.unselectable);i="up"==e?d.index(o)-c:d.index(o)+c,0<(n=("up"==e?0<=i:i<d.length)?d.eq(i):"up"==e?d.first():d.last()).length&&(g.debug("Scrolling page",e,n),o.removeClass(h.selected),n.addClass(h.selected),p.selectOnKeydown&&g.is.single()&&g.set.selectedItem(n),a.scrollTop(u))},set:{filtered:function(){var e=g.is.multiple(),t=g.is.searchSelection(),n=e&&t,i=t?g.get.query():"",o="string"==typeof i&&0<i.length,a=g.get.searchWidth(),r=""!==i;e&&o&&(g.verbose("Adjusting input width",a,p.glyphWidth),T.css("width",a)),o||n&&r?(g.verbose("Hiding placeholder text"),k.addClass(h.filtered)):(!e||n&&!r)&&(g.verbose("Showing placeholder text"),k.removeClass(h.filtered))},empty:function(){w.addClass(h.empty)},loading:function(){w.addClass(h.loading)},placeholderText:function(e){e=e||g.get.placeholderText(),g.debug("Setting placeholder text",e),g.set.text(e),k.addClass(h.placeholder)},tabbable:function(){g.is.searchSelection()?(g.debug("Added tabindex to searchable dropdown"),T.val("").attr("tabindex",0),F.attr("tabindex",-1)):(g.debug("Added tabindex to dropdown"),w.attr("tabindex")===J&&(w.attr("tabindex",0),F.attr("tabindex",-1)))},initialLoad:function(){g.verbose("Setting initial load"),e=!0},activeItem:function(e){p.allowAdditions&&0<e.filter(y.addition).length?e.addClass(h.filtered):e.addClass(h.active)},partialSearch:function(e){var t=g.get.query().length;T.val(e.substr(0,t))},scrollPosition:function(e,t){var n,i,o,a,r,s;n=(e=e||g.get.selectedItem()).closest(y.menu),i=e&&0<e.length,t=t!==J&&t,e&&0<n.length&&i&&(e.position().top,n.addClass(h.loading),o=(a=n.scrollTop())-n.offset().top+e.offset().top,t||(s=a+n.height()<o+5,r=o-5<a),g.debug("Scrolling to active item",o),(t||r||s)&&n.scrollTop(o),n.removeClass(h.loading))},text:function(e){"select"!==p.action&&("combo"==p.action?(g.debug("Changing combo button text",e,E),p.preserveHTML?E.html(e):E.text(e)):(e!==g.get.placeholderText()&&k.removeClass(h.placeholder),g.debug("Changing text",e,k),k.removeClass(h.filtered),p.preserveHTML?k.html(e):k.text(e)))},selectedItem:function(e){var t=g.get.choiceValue(e),n=g.get.choiceText(e,!1),i=g.get.choiceText(e,!0);g.debug("Setting user selection to item",e),g.remove.activeItem(),g.set.partialSearch(n),g.set.activeItem(e),g.set.selected(t,e),g.set.text(i)},selectedLetter:function(e){var t,n=O.filter("."+h.selected),i=0<n.length&&g.has.firstLetter(n,e),o=!1;i&&(t=n.nextAll(O).eq(0),g.has.firstLetter(t,e)&&(o=t)),o||O.each(function(){if(g.has.firstLetter(Y(this),e))return o=Y(this),!1}),o&&(g.verbose("Scrolling to next value with letter",e),g.set.scrollPosition(o),n.removeClass(h.selected),o.addClass(h.selected),p.selectOnKeydown&&g.is.single()&&g.set.selectedItem(o))},direction:function(e){"auto"==p.direction?(g.remove.upward(),g.can.openDownward(e)?g.remove.upward(e):g.set.upward(e),g.is.leftward(e)||g.can.openRightward(e)||g.set.leftward(e)):"upward"==p.direction&&g.set.upward(e)},upward:function(e){(e||w).addClass(h.upward)},leftward:function(e){(e||F).addClass(h.leftward)},value:function(e,t,n){var i=g.escape.value(e),o=0<R.length,a=g.get.values(),r=e!==J?String(e):e;if(o){if(!p.allowReselection&&r==a&&(g.verbose("Skipping value update already same value",e,a),!g.is.initialLoad()))return;g.is.single()&&g.has.selectInput()&&g.can.extendSelect()&&(g.debug("Adding user option",e),g.add.optionValue(e)),g.debug("Updating input value",i,a),j=!0,R.val(i),!1===p.fireOnInit&&g.is.initialLoad()?g.debug("Input native change event ignored on initial load"):g.trigger.change(),j=!1}else g.verbose("Storing value in metadata",i,R),i!==a&&w.data(b.value,r);g.is.single()&&p.clearable&&(i?g.set.clearable():g.remove.clearable()),!1===p.fireOnInit&&g.is.initialLoad()?g.verbose("No callback on initial load",p.onChange):p.onChange.call(z,e,t,n)},active:function(){w.addClass(h.active)},multiple:function(){w.addClass(h.multiple)},visible:function(){w.addClass(h.visible)},exactly:function(e,t){g.debug("Setting selected to exact values"),g.clear(),g.set.selected(e,t)},selected:function(e,s){var l=g.is.multiple();(s=p.allowAdditions?s||g.get.itemWithAdditions(e):s||g.get.item(e))&&(g.debug("Setting selected menu item to",s),g.is.multiple()&&g.remove.searchWidth(),g.is.single()?(g.remove.activeItem(),g.remove.selectedItem()):p.useLabels&&g.remove.selectedItem(),s.each(function(){var e=Y(this),t=g.get.choiceText(e),n=g.get.choiceValue(e,t),i=e.hasClass(h.filtered),o=e.hasClass(h.active),a=e.hasClass(h.addition),r=l&&1==s.length;l?!o||a?(p.apiSettings&&p.saveRemoteData&&g.save.remoteData(t,n),p.useLabels?(g.add.label(n,t,r),g.add.value(n,t,e),g.set.activeItem(e),g.filterActive(),g.select.nextAvailable(s)):(g.add.value(n,t,e),g.set.text(g.add.variables(c.count)),g.set.activeItem(e))):i||(g.debug("Selected active value, removing label"),g.remove.selected(n)):(p.apiSettings&&p.saveRemoteData&&g.save.remoteData(t,n),g.set.text(t),g.set.value(n,t,e),e.addClass(h.active).addClass(h.selected))}))},clearable:function(){P.addClass(h.clear)}},add:{label:function(e,t,n){var i,o=g.is.searchSelection()?T:k,a=g.escape.value(e);p.ignoreCase&&(a=a.toLowerCase()),i=Y("<a />").addClass(h.label).attr("data-"+b.value,a).html(m.label(a,t)),i=p.onLabelCreate.call(i,a,t),g.has.label(e)?g.debug("User selection already exists, skipping",a):(p.label.variation&&i.addClass(p.label.variation),!0===n?(g.debug("Animating in label",i),i.addClass(h.hidden).insertBefore(o).transition(p.label.transition,p.label.duration)):(g.debug("Adding selection label",i),i.insertBefore(o)))},message:function(e){var t=F.children(y.message),n=p.templates.message(g.add.variables(e));0<t.length?t.html(n):t=Y("<div/>").html(n).addClass(h.message).appendTo(F)},optionValue:function(e){var t=g.escape.value(e);0<R.find('option[value="'+g.escape.string(t)+'"]').length||(g.disconnect.selectObserver(),g.is.single()&&(g.verbose("Removing previous user addition"),R.find("option."+h.addition).remove()),Y("<option/>").prop("value",t).addClass(h.addition).html(e).appendTo(R),g.verbose("Adding user addition as an <option>",e),g.observe.select())},userSuggestion:function(e){var t,n=F.children(y.addition),i=g.get.item(e),o=i&&i.not(y.addition).length,a=0<n.length;p.useLabels&&g.has.maxSelections()||(""===e||o?n.remove():(a?(n.data(b.value,e).data(b.text,e).attr("data-"+b.value,e).attr("data-"+b.text,e).removeClass(h.filtered),p.hideAdditions||(t=p.templates.addition(g.add.variables(c.addResult,e)),n.html(t)),g.verbose("Replacing user suggestion with new value",n)):((n=g.create.userChoice(e)).prependTo(F),g.verbose("Adding item choice to menu corresponding with user choice addition",n)),p.hideAdditions&&!g.is.allFiltered()||n.addClass(h.selected).siblings().removeClass(h.selected),g.refreshItems()))},variables:function(e,t){var n,i,o=-1!==e.search("{count}"),a=-1!==e.search("{maxCount}"),r=-1!==e.search("{term}");return g.verbose("Adding templated variables to message",e),o&&(n=g.get.selectionCount(),e=e.replace("{count}",n)),a&&(n=g.get.selectionCount(),e=e.replace("{maxCount}",p.maxSelections)),r&&(i=t||g.get.query(),e=e.replace("{term}",i)),e},value:function(e,t,n){var i,o=g.get.values();g.has.value(e)?g.debug("Value already selected"):""!==e?(i=Y.isArray(o)?(i=o.concat([e]),g.get.uniqueArray(i)):[e],g.has.selectInput()?g.can.extendSelect()&&(g.debug("Adding value to select",e,i,R),g.add.optionValue(e)):(i=i.join(p.delimiter),g.debug("Setting hidden input to delimited value",i,R)),!1===p.fireOnInit&&g.is.initialLoad()?g.verbose("Skipping onadd callback on initial load",p.onAdd):p.onAdd.call(z,e,t,n),g.set.value(i,e,t,n),g.check.maxSelections()):g.debug("Cannot select blank values from multiselect")}},remove:{active:function(){w.removeClass(h.active)},activeLabel:function(){w.find(y.label).removeClass(h.active)},empty:function(){w.removeClass(h.empty)},loading:function(){w.removeClass(h.loading)},initialLoad:function(){e=!1},upward:function(e){(e||w).removeClass(h.upward)},leftward:function(e){(e||F).removeClass(h.leftward)},visible:function(){w.removeClass(h.visible)},activeItem:function(){O.removeClass(h.active)},filteredItem:function(){p.useLabels&&g.has.maxSelections()||(p.useLabels&&g.is.multiple()?O.not("."+h.active).removeClass(h.filtered):O.removeClass(h.filtered),g.remove.empty())},optionValue:function(e){var t=g.escape.value(e),n=R.find('option[value="'+g.escape.string(t)+'"]');0<n.length&&n.hasClass(h.addition)&&(r&&(r.disconnect(),g.verbose("Temporarily disconnecting mutation observer")),n.remove(),g.verbose("Removing user addition as an <option>",t),r&&r.observe(R[0],{childList:!0,subtree:!0}))},message:function(){F.children(y.message).remove()},searchWidth:function(){T.css("width","")},searchTerm:function(){g.verbose("Cleared search term"),T.val(""),g.set.filtered()},userAddition:function(){O.filter(y.addition).remove()},selected:function(e,t){if(!(t=p.allowAdditions?t||g.get.itemWithAdditions(e):t||g.get.item(e)))return!1;t.each(function(){var e=Y(this),t=g.get.choiceText(e),n=g.get.choiceValue(e,t);g.is.multiple()?p.useLabels?(g.remove.value(n,t,e),g.remove.label(n)):(g.remove.value(n,t,e),0===g.get.selectionCount()?g.set.placeholderText():g.set.text(g.add.variables(c.count))):g.remove.value(n,t,e),e.removeClass(h.filtered).removeClass(h.active),p.useLabels&&e.removeClass(h.selected)})},selectedItem:function(){O.removeClass(h.selected)},value:function(e,t,n){var i,o=g.get.values();g.has.selectInput()?(g.verbose("Input is <select> removing selected option",e),i=g.remove.arrayValue(e,o),g.remove.optionValue(e)):(g.verbose("Removing from delimited values",e),i=(i=g.remove.arrayValue(e,o)).join(p.delimiter)),!1===p.fireOnInit&&g.is.initialLoad()?g.verbose("No callback on initial load",p.onRemove):p.onRemove.call(z,e,t,n),g.set.value(i,t,n),g.check.maxSelections()},arrayValue:function(t,e){return Y.isArray(e)||(e=[e]),e=Y.grep(e,function(e){return t!=e}),g.verbose("Removed value from delimited string",t,e),e},label:function(e,t){var n=w.find(y.label).filter("[data-"+b.value+'="'+g.escape.string(e)+'"]');g.verbose("Removing label",n),n.remove()},activeLabels:function(e){e=e||w.find(y.label).filter("."+h.active),g.verbose("Removing active label selections",e),g.remove.labels(e)},labels:function(e){e=e||w.find(y.label),g.verbose("Removing labels",e),e.each(function(){var e=Y(this),t=e.data(b.value),n=t!==J?String(t):t,i=g.is.userValue(n);!1!==p.onLabelRemove.call(e,t)?(g.remove.message(),i?(g.remove.value(n),g.remove.label(n)):g.remove.selected(n)):g.debug("Label remove callback cancelled removal")})},tabbable:function(){g.is.searchSelection()?(g.debug("Searchable dropdown initialized"),T.removeAttr("tabindex")):(g.debug("Simple selection dropdown initialized"),w.removeAttr("tabindex")),F.removeAttr("tabindex")},clearable:function(){P.removeClass(h.clear)}},has:{menuSearch:function(){return g.has.search()&&0<T.closest(F).length},search:function(){return 0<T.length},sizer:function(){return 0<A.length},selectInput:function(){return R.is("select")},minCharacters:function(e){return!p.minCharacters||(e=e!==J?String(e):String(g.get.query())).length>=p.minCharacters},firstLetter:function(e,t){var n;return!(!e||0===e.length||"string"!=typeof t)&&(n=g.get.choiceText(e,!1),(t=t.toLowerCase())==String(n).charAt(0).toLowerCase())},input:function(){return 0<R.length},items:function(){return 0<O.length},menu:function(){return 0<F.length},message:function(){return 0!==F.children(y.message).length},label:function(e){var t=g.escape.value(e),n=w.find(y.label);return p.ignoreCase&&(t=t.toLowerCase()),0<n.filter("[data-"+b.value+'="'+g.escape.string(t)+'"]').length},maxSelections:function(){return p.maxSelections&&g.get.selectionCount()>=p.maxSelections},allResultsFiltered:function(){var e=O.not(y.addition);return e.filter(y.unselectable).length===e.length},userSuggestion:function(){return 0<F.children(y.addition).length},query:function(){return""!==g.get.query()},value:function(e){return p.ignoreCase?g.has.valueIgnoringCase(e):g.has.valueMatchingCase(e)},valueMatchingCase:function(e){var t=g.get.values();return!!(Y.isArray(t)?t&&-1!==Y.inArray(e,t):t==e)},valueIgnoringCase:function(n){var e=g.get.values(),i=!1;return Y.isArray(e)||(e=[e]),Y.each(e,function(e,t){if(String(n).toLowerCase()==String(t).toLowerCase())return!(i=!0)}),i}},is:{active:function(){return w.hasClass(h.active)},animatingInward:function(){return F.transition("is inward")},animatingOutward:function(){return F.transition("is outward")},bubbledLabelClick:function(e){return Y(e.target).is("select, input")&&0<w.closest("label").length},bubbledIconClick:function(e){return 0<Y(e.target).closest(P).length},alreadySetup:function(){return w.is("select")&&w.parent(y.dropdown).data(C)!==J&&0===w.prev().length},animating:function(e){return e?e.transition&&e.transition("is animating"):F.transition&&F.transition("is animating")},leftward:function(e){return(e||F).hasClass(h.leftward)},disabled:function(){return w.hasClass(h.disabled)},focused:function(){return K.activeElement===w[0]},focusedOnSearch:function(){return K.activeElement===T[0]},allFiltered:function(){return(g.is.multiple()||g.has.search())&&!(0==p.hideAdditions&&g.has.userSuggestion())&&!g.has.message()&&g.has.allResultsFiltered()},hidden:function(e){return!g.is.visible(e)},initialLoad:function(){return e},inObject:function(n,e){var i=!1;return Y.each(e,function(e,t){if(t==n)return i=!0}),i},multiple:function(){return w.hasClass(h.multiple)},remote:function(){return p.apiSettings&&g.can.useAPI()},single:function(){return!g.is.multiple()},selectMutation:function(e){var n=!1;return Y.each(e,function(e,t){if(t.target&&Y(t.target).is("select"))return n=!0}),n},search:function(){return w.hasClass(h.search)},searchSelection:function(){return g.has.search()&&1===T.parent(y.dropdown).length},selection:function(){return w.hasClass(h.selection)},userValue:function(e){return-1!==Y.inArray(e,g.get.userValues())},upward:function(e){return(e||w).hasClass(h.upward)},visible:function(e){return e?e.hasClass(h.visible):F.hasClass(h.visible)},verticallyScrollableContext:function(){var e=S.get(0)!==Z&&S.css("overflow-y");return"auto"==e||"scroll"==e},horizontallyScrollableContext:function(){var e=S.get(0)!==Z&&S.css("overflow-X");return"auto"==e||"scroll"==e}},can:{activate:function(e){return!!p.useLabels||(!g.has.maxSelections()||!(!g.has.maxSelections()||!e.hasClass(h.active)))},openDownward:function(e){var t,n,i=e||F,o=!0;return i.addClass(h.loading),n={context:{offset:S.get(0)===Z?{top:0,left:0}:S.offset(),scrollTop:S.scrollTop(),height:S.outerHeight()},menu:{offset:i.offset(),height:i.outerHeight()}},g.is.verticallyScrollableContext()&&(n.menu.offset.top+=n.context.scrollTop),o=(t={above:n.context.scrollTop<=n.menu.offset.top-n.context.offset.top-n.menu.height,below:n.context.scrollTop+n.context.height>=n.menu.offset.top-n.context.offset.top+n.menu.height}).below?(g.verbose("Dropdown can fit in context downward",t),!0):t.below||t.above?(g.verbose("Dropdown cannot fit below, opening upward",t),!1):(g.verbose("Dropdown cannot fit in either direction, favoring downward",t),!0),i.removeClass(h.loading),o},openRightward:function(e){var t,n,i=e||F,o=!0;return i.addClass(h.loading),n={context:{offset:S.get(0)===Z?{top:0,left:0}:S.offset(),scrollLeft:S.scrollLeft(),width:S.outerWidth()},menu:{offset:i.offset(),width:i.outerWidth()}},g.is.horizontallyScrollableContext()&&(n.menu.offset.left+=n.context.scrollLeft),(t=n.menu.offset.left-n.context.offset.left+n.menu.width>=n.context.scrollLeft+n.context.width)&&(g.verbose("Dropdown cannot fit in context rightward",t),o=!1),i.removeClass(h.loading),o},click:function(){return U||"click"==p.on},extendSelect:function(){return p.allowAdditions||p.apiSettings},show:function(){return!g.is.disabled()&&(g.has.items()||g.has.message())},useAPI:function(){return Y.fn.api!==J}},animate:{show:function(e,t){var n,i=t||F,o=t?function(){}:function(){g.hideSubMenus(),g.hideOthers(),g.set.active()};e=Y.isFunction(e)?e:function(){},g.verbose("Doing menu show animation",i),g.set.direction(t),n=g.get.transition(t),g.is.selection()&&g.set.scrollPosition(g.get.selectedItem(),!0),(g.is.hidden(i)||g.is.animating(i))&&("none"==n?(o(),i.transition("show"),e.call(z)):Y.fn.transition!==J&&w.transition("is supported")?i.transition({animation:n+" in",debug:p.debug,verbose:p.verbose,duration:p.duration,queue:!0,onStart:o,onComplete:function(){e.call(z)}}):g.error(f.noTransition,n))},hide:function(e,t){var n=t||F,i=(t?p.duration:p.duration,t?function(){}:function(){g.can.click()&&g.unbind.intent(),g.remove.active()}),o=g.get.transition(t);e=Y.isFunction(e)?e:function(){},(g.is.visible(n)||g.is.animating(n))&&(g.verbose("Doing menu hide animation",n),"none"==o?(i(),n.transition("hide"),e.call(z)):Y.fn.transition!==J&&w.transition("is supported")?n.transition({animation:o+" out",duration:p.duration,debug:p.debug,verbose:p.verbose,queue:!1,onStart:i,onComplete:function(){e.call(z)}}):g.error(f.transition))}},hideAndClear:function(){g.remove.searchTerm(),g.has.maxSelections()||(g.has.search()?g.hide(function(){g.remove.filteredItem()}):g.hide())},delay:{show:function(){g.verbose("Delaying show event to ensure user intent"),clearTimeout(g.timer),g.timer=setTimeout(g.show,p.delay.show)},hide:function(){g.verbose("Delaying hide event to ensure user intent"),clearTimeout(g.timer),g.timer=setTimeout(g.hide,p.delay.hide)}},escape:{value:function(e){var t=Y.isArray(e),n="string"==typeof e,i=!n&&!t,o=n&&-1!==e.search(d.quote),a=[];return i||!o?e:(g.debug("Encoding quote values for use in select",e),t?(Y.each(e,function(e,t){a.push(t.replace(d.quote,"&quot;"))}),a):e.replace(d.quote,"&quot;"))},string:function(e){return(e=String(e)).replace(d.escape,"\\$&")}},setting:function(e,t){if(g.debug("Changing setting",e,t),Y.isPlainObject(e))Y.extend(!0,p,e);else{if(t===J)return p[e];Y.isPlainObject(p[e])?Y.extend(!0,p[e],t):p[e]=t}},internal:function(e,t){if(Y.isPlainObject(e))Y.extend(!0,g,e);else{if(t===J)return g[e];g[e]=t}},debug:function(){!p.silent&&p.debug&&(p.performance?g.performance.log(arguments):(g.debug=Function.prototype.bind.call(console.info,console,p.name+":"),g.debug.apply(console,arguments)))},verbose:function(){!p.silent&&p.verbose&&p.debug&&(p.performance?g.performance.log(arguments):(g.verbose=Function.prototype.bind.call(console.info,console,p.name+":"),g.verbose.apply(console,arguments)))},error:function(){p.silent||(g.error=Function.prototype.bind.call(console.error,console,p.name+":"),g.error.apply(console,arguments))},performance:{log:function(e){var t,n;p.performance&&(n=(t=(new Date).getTime())-(W||t),W=t,B.push({Name:e[0],Arguments:[].slice.call(e,1)||"",Element:z,"Execution Time":n})),clearTimeout(g.performance.timer),g.performance.timer=setTimeout(g.performance.display,500)},display:function(){var e=p.name+":",n=0;W=!1,clearTimeout(g.performance.timer),Y.each(B,function(e,t){n+=t["Execution Time"]}),e+=" "+n+"ms",H&&(e+=" '"+H+"'"),(console.group!==J||console.table!==J)&&0<B.length&&(console.groupCollapsed(e),console.table?console.table(B):Y.each(B,function(e,t){console.log(t.Name+": "+t["Execution Time"]+"ms")}),console.groupEnd()),B=[]}},invoke:function(i,e,t){var o,a,n,r=I;return e=e||$,t=z||t,"string"==typeof i&&r!==J&&(i=i.split(/[\. ]/),o=i.length-1,Y.each(i,function(e,t){var n=e!=o?t+i[e+1].charAt(0).toUpperCase()+i[e+1].slice(1):i;if(Y.isPlainObject(r[n])&&e!=o)r=r[n];else{if(r[n]!==J)return a=r[n],!1;if(!Y.isPlainObject(r[t])||e==o)return r[t]!==J?a=r[t]:g.error(f.method,i),!1;r=r[t]}})),Y.isFunction(a)?n=a.apply(t,e):a!==J&&(n=a),Y.isArray(L)?L.push(n):L!==J?L=[L,n]:n!==J&&(L=n),a}},X?(I===J&&g.initialize(),g.invoke(Q)):(I!==J&&I.invoke("destroy"),g.initialize())}),L!==J?L:V},Y.fn.dropdown.settings={silent:!1,debug:!1,verbose:!1,performance:!0,on:"click",action:"activate",values:!1,clearable:!1,apiSettings:!1,selectOnKeydown:!0,minCharacters:0,filterRemoteData:!1,saveRemoteData:!0,throttle:200,context:Z,direction:"auto",keepOnScreen:!0,match:"both",fullTextSearch:!1,placeholder:"auto",preserveHTML:!0,sortSelect:!1,forceSelection:!0,allowAdditions:!1,ignoreCase:!1,hideAdditions:!0,maxSelections:!1,useLabels:!0,delimiter:",",showOnFocus:!0,allowReselection:!1,allowTab:!0,allowCategorySelection:!1,fireOnInit:!1,transition:"auto",duration:200,glyphWidth:1.037,label:{transition:"scale",duration:200,variation:!1},delay:{hide:300,show:200,search:20,touch:50},onChange:function(e,t,n){},onAdd:function(e,t,n){},onRemove:function(e,t,n){},onLabelSelect:function(e){},onLabelCreate:function(e,t){return Y(this)},onLabelRemove:function(e){return!0},onNoResults:function(e){return!0},onShow:function(){},onHide:function(){},name:"Dropdown",namespace:"dropdown",message:{addResult:"Add <b>{term}</b>",count:"{count} selected",maxSelections:"Max {maxCount} selections",noResults:"No results found.",serverError:"There was an error contacting the server"},error:{action:"You called a dropdown action that was not defined",alreadySetup:"Once a select has been initialized behaviors must be called on the created ui dropdown",labels:"Allowing user additions currently requires the use of labels.",missingMultiple:"<select> requires multiple property to be set to correctly preserve multiple values",method:"The method you called is not defined.",noAPI:"The API module is required to load resources remotely",noStorage:"Saving remote data requires session storage",noTransition:"This module requires ui transitions <https://github.com/Semantic-Org/UI-Transition>"},regExp:{escape:/[-[\]{}()*+?.,\\^$|#\s]/g,quote:/"/g},metadata:{defaultText:"defaultText",defaultValue:"defaultValue",placeholderText:"placeholder",text:"text",value:"value"},fields:{remoteValues:"results",values:"values",disabled:"disabled",name:"name",value:"value",text:"text"},keys:{backspace:8,delimiter:188,deleteKey:46,enter:13,escape:27,pageUp:33,pageDown:34,leftArrow:37,upArrow:38,rightArrow:39,downArrow:40},selector:{addition:".addition",dropdown:".ui.dropdown",hidden:".hidden",icon:"> .dropdown.icon",input:'> input[type="hidden"], > select',item:".item",label:"> .label",remove:"> .label > .delete.icon",siblingLabel:".label",menu:".menu",message:".message",menuIcon:".dropdown.icon",search:"input.search, .menu > .search > input, .menu input.search",sizer:"> input.sizer",text:"> .text:not(.icon)",unselectable:".disabled, .filtered"},className:{active:"active",addition:"addition",animating:"animating",clear:"clear",disabled:"disabled",empty:"empty",dropdown:"ui dropdown",filtered:"filtered",hidden:"hidden transition",item:"item",label:"ui label",loading:"loading",menu:"menu",message:"message",multiple:"multiple",placeholder:"default",sizer:"sizer",search:"search",selected:"selected",selection:"selection",upward:"upward",leftward:"left",visible:"visible"}},Y.fn.dropdown.settings.templates={dropdown:function(e){var t=e.placeholder||!1,n=(e.values,"");return n+='<i class="dropdown icon"></i>',e.placeholder?n+='<div class="default text">'+t+"</div>":n+='<div class="text"></div>',n+='<div class="menu">',Y.each(e.values,function(e,t){n+=t.disabled?'<div class="disabled item" data-value="'+t.value+'">'+t.name+"</div>":'<div class="item" data-value="'+t.value+'">'+t.name+"</div>"}),n+="</div>"},menu:function(e,o){var t=e[o.values]||{},a="";return Y.each(t,function(e,t){var n=t[o.text]?'data-text="'+t[o.text]+'"':"",i=t[o.disabled]?"disabled ":"";a+='<div class="'+i+'item" data-value="'+t[o.value]+'"'+n+">",a+=t[o.name],a+="</div>"}),a},label:function(e,t){return t+'<i class="delete icon"></i>'},message:function(e){return e},addition:function(e){return e}}}(jQuery,window,document),function(k,T,e,A){"use strict";T=void 0!==T&&T.Math==Math?T:"undefined"!=typeof self&&self.Math==Math?self:Function("return this")(),k.fn.embed=function(p){var h,v=k(this),b=v.selector||"",y=(new Date).getTime(),x=[],C=p,w="string"==typeof C,S=[].slice.call(arguments,1);return v.each(function(){var s,i=k.isPlainObject(p)?k.extend(!0,{},k.fn.embed.settings,p):k.extend({},k.fn.embed.settings),e=i.selector,t=i.className,o=i.sources,l=i.error,a=i.metadata,n=i.namespace,r=i.templates,c="."+n,u="module-"+n,d=(k(T),k(this)),f=(d.find(e.placeholder),d.find(e.icon),d.find(e.embed)),m=this,g=d.data(u);s={initialize:function(){s.debug("Initializing embed"),s.determine.autoplay(),s.create(),s.bind.events(),s.instantiate()},instantiate:function(){s.verbose("Storing instance of module",s),g=s,d.data(u,s)},destroy:function(){s.verbose("Destroying previous instance of embed"),s.reset(),d.removeData(u).off(c)},refresh:function(){s.verbose("Refreshing selector cache"),d.find(e.placeholder),d.find(e.icon),f=d.find(e.embed)},bind:{events:function(){s.has.placeholder()&&(s.debug("Adding placeholder events"),d.on("click"+c,e.placeholder,s.createAndShow).on("click"+c,e.icon,s.createAndShow))}},create:function(){s.get.placeholder()?s.createPlaceholder():s.createAndShow()},createPlaceholder:function(e){var t=s.get.icon(),n=s.get.url();s.generate.embed(n);e=e||s.get.placeholder(),d.html(r.placeholder(e,t)),s.debug("Creating placeholder for embed",e,t)},createEmbed:function(e){s.refresh(),e=e||s.get.url(),f=k("<div/>").addClass(t.embed).html(s.generate.embed(e)).appendTo(d),i.onCreate.call(m,e),s.debug("Creating embed object",f)},changeEmbed:function(e){f.html(s.generate.embed(e))},createAndShow:function(){s.createEmbed(),s.show()},change:function(e,t,n){s.debug("Changing video to ",e,t,n),d.data(a.source,e).data(a.id,t),n?d.data(a.url,n):d.removeData(a.url),s.has.embed()?s.changeEmbed():s.create()},reset:function(){s.debug("Clearing embed and showing placeholder"),s.remove.data(),s.remove.active(),s.remove.embed(),s.showPlaceholder(),i.onReset.call(m)},show:function(){s.debug("Showing embed"),s.set.active(),i.onDisplay.call(m)},hide:function(){s.debug("Hiding embed"),s.showPlaceholder()},showPlaceholder:function(){s.debug("Showing placeholder image"),s.remove.active(),i.onPlaceholderDisplay.call(m)},get:{id:function(){return i.id||d.data(a.id)},placeholder:function(){return i.placeholder||d.data(a.placeholder)},icon:function(){return i.icon?i.icon:d.data(a.icon)!==A?d.data(a.icon):s.determine.icon()},source:function(e){return i.source?i.source:d.data(a.source)!==A?d.data(a.source):s.determine.source()},type:function(){var e=s.get.source();return o[e]!==A&&o[e].type},url:function(){return i.url?i.url:d.data(a.url)!==A?d.data(a.url):s.determine.url()}},determine:{autoplay:function(){s.should.autoplay()&&(i.autoplay=!0)},source:function(n){var i=!1;return(n=n||s.get.url())&&k.each(o,function(e,t){if(-1!==n.search(t.domain))return i=e,!1}),i},icon:function(){var e=s.get.source();return o[e]!==A&&o[e].icon},url:function(){var e,t=i.id||d.data(a.id),n=i.source||d.data(a.source);return(e=o[n]!==A&&o[n].url.replace("{id}",t))&&d.data(a.url,e),e}},set:{active:function(){d.addClass(t.active)}},remove:{data:function(){d.removeData(a.id).removeData(a.icon).removeData(a.placeholder).removeData(a.source).removeData(a.url)},active:function(){d.removeClass(t.active)},embed:function(){f.empty()}},encode:{parameters:function(e){var t,n=[];for(t in e)n.push(encodeURIComponent(t)+"="+encodeURIComponent(e[t]));return n.join("&amp;")}},generate:{embed:function(e){s.debug("Generating embed html");var t,n,i=s.get.source();return(e=s.get.url(e))?(n=s.generate.parameters(i),t=r.iframe(e,n)):s.error(l.noURL,d),t},parameters:function(e,t){var n=o[e]&&o[e].parameters!==A?o[e].parameters(i):{};return(t=t||i.parameters)&&(n=k.extend({},n,t)),n=i.onEmbed(n),s.encode.parameters(n)}},has:{embed:function(){return 0<f.length},placeholder:function(){return i.placeholder||d.data(a.placeholder)}},should:{autoplay:function(){return"auto"===i.autoplay?i.placeholder||d.data(a.placeholder)!==A:i.autoplay}},is:{video:function(){return"video"==s.get.type()}},setting:function(e,t){if(s.debug("Changing setting",e,t),k.isPlainObject(e))k.extend(!0,i,e);else{if(t===A)return i[e];k.isPlainObject(i[e])?k.extend(!0,i[e],t):i[e]=t}},internal:function(e,t){if(k.isPlainObject(e))k.extend(!0,s,e);else{if(t===A)return s[e];s[e]=t}},debug:function(){!i.silent&&i.debug&&(i.performance?s.performance.log(arguments):(s.debug=Function.prototype.bind.call(console.info,console,i.name+":"),s.debug.apply(console,arguments)))},verbose:function(){!i.silent&&i.verbose&&i.debug&&(i.performance?s.performance.log(arguments):(s.verbose=Function.prototype.bind.call(console.info,console,i.name+":"),s.verbose.apply(console,arguments)))},error:function(){i.silent||(s.error=Function.prototype.bind.call(console.error,console,i.name+":"),s.error.apply(console,arguments))},performance:{log:function(e){var t,n;i.performance&&(n=(t=(new Date).getTime())-(y||t),y=t,x.push({Name:e[0],Arguments:[].slice.call(e,1)||"",Element:m,"Execution Time":n})),clearTimeout(s.performance.timer),s.performance.timer=setTimeout(s.performance.display,500)},display:function(){var e=i.name+":",n=0;y=!1,clearTimeout(s.performance.timer),k.each(x,function(e,t){n+=t["Execution Time"]}),e+=" "+n+"ms",b&&(e+=" '"+b+"'"),1<v.length&&(e+=" ("+v.length+")"),(console.group!==A||console.table!==A)&&0<x.length&&(console.groupCollapsed(e),console.table?console.table(x):k.each(x,function(e,t){console.log(t.Name+": "+t["Execution Time"]+"ms")}),console.groupEnd()),x=[]}},invoke:function(i,e,t){var o,a,n,r=g;return e=e||S,t=m||t,"string"==typeof i&&r!==A&&(i=i.split(/[\. ]/),o=i.length-1,k.each(i,function(e,t){var n=e!=o?t+i[e+1].charAt(0).toUpperCase()+i[e+1].slice(1):i;if(k.isPlainObject(r[n])&&e!=o)r=r[n];else{if(r[n]!==A)return a=r[n],!1;if(!k.isPlainObject(r[t])||e==o)return r[t]!==A?a=r[t]:s.error(l.method,i),!1;r=r[t]}})),k.isFunction(a)?n=a.apply(t,e):a!==A&&(n=a),k.isArray(h)?h.push(n):h!==A?h=[h,n]:n!==A&&(h=n),a}},w?(g===A&&s.initialize(),s.invoke(C)):(g!==A&&g.invoke("destroy"),s.initialize())}),h!==A?h:this},k.fn.embed.settings={name:"Embed",namespace:"embed",silent:!1,debug:!1,verbose:!1,performance:!0,icon:!1,source:!1,url:!1,id:!1,autoplay:"auto",color:"#444444",hd:!0,brandedUI:!1,parameters:!1,onDisplay:function(){},onPlaceholderDisplay:function(){},onReset:function(){},onCreate:function(e){},onEmbed:function(e){return e},metadata:{id:"id",icon:"icon",placeholder:"placeholder",source:"source",url:"url"},error:{noURL:"No URL specified",method:"The method you called is not defined"},className:{active:"active",embed:"embed"},selector:{embed:".embed",placeholder:".placeholder",icon:".icon"},sources:{youtube:{name:"youtube",type:"video",icon:"video play",domain:"youtube.com",url:"//www.youtube.com/embed/{id}",parameters:function(e){return{autohide:!e.brandedUI,autoplay:e.autoplay,color:e.color||A,hq:e.hd,jsapi:e.api,modestbranding:!e.brandedUI}}},vimeo:{name:"vimeo",type:"video",icon:"video play",domain:"vimeo.com",url:"//player.vimeo.com/video/{id}",parameters:function(e){return{api:e.api,autoplay:e.autoplay,byline:e.brandedUI,color:e.color||A,portrait:e.brandedUI,title:e.brandedUI}}}},templates:{iframe:function(e,t){var n=e;return t&&(n+="?"+t),'<iframe src="'+n+'" width="100%" height="100%" frameborder="0" scrolling="no" webkitAllowFullScreen mozallowfullscreen allowFullScreen></iframe>'},placeholder:function(e,t){var n="";return t&&(n+='<i class="'+t+' icon"></i>'),e&&(n+='<img class="placeholder" src="'+e+'">'),n}},api:!1,onPause:function(){},onPlay:function(){},onStop:function(){}}}(jQuery,window,document),function(j,z,I,M){"use strict";z=void 0!==z&&z.Math==Math?z:"undefined"!=typeof self&&self.Math==Math?self:Function("return this")(),j.fn.modal=function(w){var S,e=j(this),k=j(z),T=j(I),A=j("body"),R=e.selector||"",P=(new Date).getTime(),E=[],F=w,O="string"==typeof F,D=[].slice.call(arguments,1),q=z.requestAnimationFrame||z.mozRequestAnimationFrame||z.webkitRequestAnimationFrame||z.msRequestAnimationFrame||function(e){setTimeout(e,0)};return e.each(function(){var n,i,e,o,a,t,r,s,l,c=j.isPlainObject(w)?j.extend(!0,{},j.fn.modal.settings,w):j.extend({},j.fn.modal.settings),u=c.selector,d=c.className,f=c.namespace,m=c.error,g="."+f,p="module-"+f,h=j(this),v=j(c.context),b=h.find(u.close),y=this,x=h.data(p),C=!1;l={initialize:function(){l.verbose("Initializing dimmer",v),l.create.id(),l.create.dimmer(),l.refreshModals(),l.bind.events(),c.observeChanges&&l.observeChanges(),l.instantiate()},instantiate:function(){l.verbose("Storing instance of modal"),x=l,h.data(p,x)},create:{dimmer:function(){var e={debug:c.debug,variation:!c.centered&&"top aligned",dimmerName:"modals"},t=j.extend(!0,e,c.dimmerSettings);j.fn.dimmer!==M?(l.debug("Creating dimmer"),o=v.dimmer(t),c.detachable?(l.verbose("Modal is detachable, moving content into dimmer"),o.dimmer("add content",h)):l.set.undetached(),a=o.dimmer("get dimmer")):l.error(m.dimmer)},id:function(){r=(Math.random().toString(16)+"000000000").substr(2,8),t="."+r,l.verbose("Creating unique id for element",r)}},destroy:function(){l.verbose("Destroying previous modal"),h.removeData(p).off(g),k.off(t),a.off(t),b.off(g),v.dimmer("destroy")},observeChanges:function(){"MutationObserver"in z&&((s=new MutationObserver(function(e){l.debug("DOM tree modified, refreshing"),l.refresh()})).observe(y,{childList:!0,subtree:!0}),l.debug("Setting up mutation observer",s))},refresh:function(){l.remove.scrolling(),l.cacheSizes(),l.can.useFlex()||l.set.modalOffset(),l.set.screenHeight(),l.set.type()},refreshModals:function(){i=h.siblings(u.modal),n=i.add(h)},attachEvents:function(e,t){var n=j(e);t=j.isFunction(l[t])?l[t]:l.toggle,0<n.length?(l.debug("Attaching modal events to element",e,t),n.off(g).on("click"+g,t)):l.error(m.notFound,e)},bind:{events:function(){l.verbose("Attaching events"),h.on("click"+g,u.close,l.event.close).on("click"+g,u.approve,l.event.approve).on("click"+g,u.deny,l.event.deny),k.on("resize"+t,l.event.resize)},scrollLock:function(){o.get(0).addEventListener("touchmove",l.event.preventScroll,{passive:!1})}},unbind:{scrollLock:function(){o.get(0).removeEventListener("touchmove",l.event.preventScroll,{passive:!1})}},get:{id:function(){return(Math.random().toString(16)+"000000000").substr(2,8)}},event:{approve:function(){C||!1===c.onApprove.call(y,j(this))?l.verbose("Approve callback returned false cancelling hide"):(C=!0,l.hide(function(){C=!1}))},preventScroll:function(e){e.preventDefault()},deny:function(){C||!1===c.onDeny.call(y,j(this))?l.verbose("Deny callback returned false cancelling hide"):(C=!0,l.hide(function(){C=!1}))},close:function(){l.hide()},click:function(e){if(c.closable){var t=0<j(e.target).closest(u.modal).length,n=j.contains(I.documentElement,e.target);!t&&n&&l.is.active()&&(l.debug("Dimmer clicked, hiding all modals"),l.remove.clickaway(),c.allowMultiple?l.hide():l.hideAll())}else l.verbose("Dimmer clicked but closable setting is disabled")},debounce:function(e,t){clearTimeout(l.timer),l.timer=setTimeout(e,t)},keyboard:function(e){27==e.which&&(c.closable?(l.debug("Escape key pressed hiding modal"),l.hide()):l.debug("Escape key pressed, but closable is set to false"),e.preventDefault())},resize:function(){o.dimmer("is active")&&(l.is.animating()||l.is.active())&&q(l.refresh)}},toggle:function(){l.is.active()||l.is.animating()?l.hide():l.show()},show:function(e){e=j.isFunction(e)?e:function(){},l.refreshModals(),l.set.dimmerSettings(),l.set.dimmerStyles(),l.showModal(e)},hide:function(e){e=j.isFunction(e)?e:function(){},l.refreshModals(),l.hideModal(e)},showModal:function(e){e=j.isFunction(e)?e:function(){},l.is.animating()||!l.is.active()?(l.showDimmer(),l.cacheSizes(),l.can.useFlex()?l.remove.legacy():(l.set.legacy(),l.set.modalOffset(),l.debug("Using non-flex legacy modal positioning.")),l.set.screenHeight(),l.set.type(),l.set.clickaway(),!c.allowMultiple&&l.others.active()?l.hideOthers(l.showModal):(c.allowMultiple&&c.detachable&&h.detach().appendTo(a),c.onShow.call(y),c.transition&&j.fn.transition!==M&&h.transition("is supported")?(l.debug("Showing modal with css animations"),h.transition({debug:c.debug,animation:c.transition+" in",queue:c.queue,duration:c.duration,useFailSafe:!0,onComplete:function(){c.onVisible.apply(y),c.keyboardShortcuts&&l.add.keyboardShortcuts(),l.save.focus(),l.set.active(),c.autofocus&&l.set.autofocus(),e()}})):l.error(m.noTransition))):l.debug("Modal is already visible")},hideModal:function(e,t){e=j.isFunction(e)?e:function(){},l.debug("Hiding modal"),!1!==c.onHide.call(y,j(this))?(l.is.animating()||l.is.active())&&(c.transition&&j.fn.transition!==M&&h.transition("is supported")?(l.remove.active(),h.transition({debug:c.debug,animation:c.transition+" out",queue:c.queue,duration:c.duration,useFailSafe:!0,onStart:function(){l.others.active()||t||l.hideDimmer(),c.keyboardShortcuts&&l.remove.keyboardShortcuts()},onComplete:function(){c.onHidden.call(y),l.remove.dimmerStyles(),l.restore.focus(),e()}})):l.error(m.noTransition)):l.verbose("Hide callback returned false cancelling hide")},showDimmer:function(){o.dimmer("is animating")||!o.dimmer("is active")?(l.debug("Showing dimmer"),o.dimmer("show")):l.debug("Dimmer already visible")},hideDimmer:function(){o.dimmer("is animating")||o.dimmer("is active")?(l.unbind.scrollLock(),o.dimmer("hide",function(){l.remove.clickaway(),l.remove.screenHeight()})):l.debug("Dimmer is not visible cannot hide")},hideAll:function(e){var t=n.filter("."+d.active+", ."+d.animating);e=j.isFunction(e)?e:function(){},0<t.length&&(l.debug("Hiding all visible modals"),l.hideDimmer(),t.modal("hide modal",e))},hideOthers:function(e){var t=i.filter("."+d.active+", ."+d.animating);e=j.isFunction(e)?e:function(){},0<t.length&&(l.debug("Hiding other modals",i),t.modal("hide modal",e,!0))},others:{active:function(){return 0<i.filter("."+d.active).length},animating:function(){return 0<i.filter("."+d.animating).length}},add:{keyboardShortcuts:function(){l.verbose("Adding keyboard shortcuts"),T.on("keyup"+g,l.event.keyboard)}},save:{focus:function(){0<j(I.activeElement).closest(h).length||(e=j(I.activeElement).blur())}},restore:{focus:function(){e&&0<e.length&&e.focus()}},remove:{active:function(){h.removeClass(d.active)},legacy:function(){h.removeClass(d.legacy)},clickaway:function(){a.off("click"+t)},dimmerStyles:function(){a.removeClass(d.inverted),o.removeClass(d.blurring)},bodyStyle:function(){""===A.attr("style")&&(l.verbose("Removing style attribute"),A.removeAttr("style"))},screenHeight:function(){l.debug("Removing page height"),A.css("height","")},keyboardShortcuts:function(){l.verbose("Removing keyboard shortcuts"),T.off("keyup"+g)},scrolling:function(){o.removeClass(d.scrolling),h.removeClass(d.scrolling)}},cacheSizes:function(){h.addClass(d.loading);var e=h.prop("scrollHeight"),t=h.outerWidth(),n=h.outerHeight();l.cache!==M&&0===n||(l.cache={pageHeight:j(I).outerHeight(),width:t,height:n+c.offset,scrollHeight:e+c.offset,contextHeight:"body"==c.context?j(z).height():o.height()},l.cache.topOffset=-l.cache.height/2),h.removeClass(d.loading),l.debug("Caching modal and container sizes",l.cache)},can:{useFlex:function(){return"auto"==c.useFlex?c.detachable&&!l.is.ie():c.useFlex},fit:function(){var e=l.cache.contextHeight,t=l.cache.contextHeight/2,n=l.cache.topOffset,i=l.cache.scrollHeight,o=l.cache.height,a=c.padding;return o<i?t+n+i+a<e:o+2*a<e}},is:{active:function(){return h.hasClass(d.active)},ie:function(){return!z.ActiveXObject&&"ActiveXObject"in z||"ActiveXObject"in z},animating:function(){return h.transition("is supported")?h.transition("is animating"):h.is(":visible")},scrolling:function(){return o.hasClass(d.scrolling)},modernBrowser:function(){return!(z.ActiveXObject||"ActiveXObject"in z)}},set:{autofocus:function(){var e=h.find("[tabindex], :input").filter(":visible"),t=e.filter("[autofocus]"),n=0<t.length?t.first():e.first();0<n.length&&n.focus()},clickaway:function(){a.on("click"+t,l.event.click)},dimmerSettings:function(){if(j.fn.dimmer!==M){var e={debug:c.debug,dimmerName:"modals",closable:"auto",useFlex:l.can.useFlex(),variation:!c.centered&&"top aligned",duration:{show:c.duration,hide:c.duration}},t=j.extend(!0,e,c.dimmerSettings);c.inverted&&(t.variation=t.variation!==M?t.variation+" inverted":"inverted"),v.dimmer("setting",t)}else l.error(m.dimmer)},dimmerStyles:function(){c.inverted?a.addClass(d.inverted):a.removeClass(d.inverted),c.blurring?o.addClass(d.blurring):o.removeClass(d.blurring)},modalOffset:function(){var e=l.cache.width,t=l.cache.height;h.css({marginTop:c.centered&&l.can.fit()?-t/2:0,marginLeft:-e/2}),l.verbose("Setting modal offset for legacy mode")},screenHeight:function(){l.can.fit()?A.css("height",""):(l.debug("Modal is taller than page content, resizing page height"),A.css("height",l.cache.height+2*c.padding))},active:function(){h.addClass(d.active)},scrolling:function(){o.addClass(d.scrolling),h.addClass(d.scrolling),l.unbind.scrollLock()},legacy:function(){h.addClass(d.legacy)},type:function(){l.can.fit()?(l.verbose("Modal fits on screen"),l.others.active()||l.others.animating()||(l.remove.scrolling(),l.bind.scrollLock())):(l.verbose("Modal cannot fit on screen setting to scrolling"),l.set.scrolling())},undetached:function(){o.addClass(d.undetached)}},setting:function(e,t){if(l.debug("Changing setting",e,t),j.isPlainObject(e))j.extend(!0,c,e);else{if(t===M)return c[e];j.isPlainObject(c[e])?j.extend(!0,c[e],t):c[e]=t}},internal:function(e,t){if(j.isPlainObject(e))j.extend(!0,l,e);else{if(t===M)return l[e];l[e]=t}},debug:function(){!c.silent&&c.debug&&(c.performance?l.performance.log(arguments):(l.debug=Function.prototype.bind.call(console.info,console,c.name+":"),l.debug.apply(console,arguments)))},verbose:function(){!c.silent&&c.verbose&&c.debug&&(c.performance?l.performance.log(arguments):(l.verbose=Function.prototype.bind.call(console.info,console,c.name+":"),l.verbose.apply(console,arguments)))},error:function(){c.silent||(l.error=Function.prototype.bind.call(console.error,console,c.name+":"),l.error.apply(console,arguments))},performance:{log:function(e){var t,n;c.performance&&(n=(t=(new Date).getTime())-(P||t),P=t,E.push({Name:e[0],Arguments:[].slice.call(e,1)||"",Element:y,"Execution Time":n})),clearTimeout(l.performance.timer),l.performance.timer=setTimeout(l.performance.display,500)},display:function(){var e=c.name+":",n=0;P=!1,clearTimeout(l.performance.timer),j.each(E,function(e,t){n+=t["Execution Time"]}),e+=" "+n+"ms",R&&(e+=" '"+R+"'"),(console.group!==M||console.table!==M)&&0<E.length&&(console.groupCollapsed(e),console.table?console.table(E):j.each(E,function(e,t){console.log(t.Name+": "+t["Execution Time"]+"ms")}),console.groupEnd()),E=[]}},invoke:function(i,e,t){var o,a,n,r=x;return e=e||D,t=y||t,"string"==typeof i&&r!==M&&(i=i.split(/[\. ]/),o=i.length-1,j.each(i,function(e,t){var n=e!=o?t+i[e+1].charAt(0).toUpperCase()+i[e+1].slice(1):i;if(j.isPlainObject(r[n])&&e!=o)r=r[n];else{if(r[n]!==M)return a=r[n],!1;if(!j.isPlainObject(r[t])||e==o)return r[t]!==M&&(a=r[t]),!1;r=r[t]}})),j.isFunction(a)?n=a.apply(t,e):a!==M&&(n=a),j.isArray(S)?S.push(n):S!==M?S=[S,n]:n!==M&&(S=n),a}},O?(x===M&&l.initialize(),l.invoke(F)):(x!==M&&x.invoke("destroy"),l.initialize())}),S!==M?S:this},j.fn.modal.settings={name:"Modal",namespace:"modal",useFlex:"auto",offset:0,silent:!1,debug:!1,verbose:!1,performance:!0,observeChanges:!1,allowMultiple:!1,detachable:!0,closable:!0,autofocus:!0,inverted:!1,blurring:!1,centered:!0,dimmerSettings:{closable:!1,useCSS:!0},keyboardShortcuts:!0,context:"body",queue:!1,duration:500,transition:"scale",padding:50,onShow:function(){},onVisible:function(){},onHide:function(){return!0},onHidden:function(){},onApprove:function(){return!0},onDeny:function(){return!0},selector:{close:"> .close",approve:".actions .positive, .actions .approve, .actions .ok",deny:".actions .negative, .actions .deny, .actions .cancel",modal:".ui.modal"},error:{dimmer:"UI Dimmer, a required component is not included in this page",method:"The method you called is not defined.",notFound:"The element you specified could not be found"},className:{active:"active",animating:"animating",blurring:"blurring",inverted:"inverted",legacy:"legacy",loading:"loading",scrolling:"scrolling",undetached:"undetached"}}}(jQuery,window,document),function(y,x,e,C){"use strict";x=void 0!==x&&x.Math==Math?x:"undefined"!=typeof self&&self.Math==Math?self:Function("return this")(),y.fn.nag=function(d){var f,e=y(this),m=e.selector||"",g=(new Date).getTime(),p=[],h=d,v="string"==typeof h,b=[].slice.call(arguments,1);return e.each(function(){var s,i=y.isPlainObject(d)?y.extend(!0,{},y.fn.nag.settings,d):y.extend({},y.fn.nag.settings),e=(i.className,i.selector),l=i.error,t=i.namespace,n="."+t,o=t+"-module",a=y(this),r=(a.find(e.close),i.context?y(i.context):y("body")),c=this,u=a.data(o);x.requestAnimationFrame||x.mozRequestAnimationFrame||x.webkitRequestAnimationFrame||x.msRequestAnimationFrame;s={initialize:function(){s.verbose("Initializing element"),a.on("click"+n,e.close,s.dismiss).data(o,s),i.detachable&&a.parent()[0]!==r[0]&&a.detach().prependTo(r),0<i.displayTime&&setTimeout(s.hide,i.displayTime),s.show()},destroy:function(){s.verbose("Destroying instance"),a.removeData(o).off(n)},show:function(){s.should.show()&&!a.is(":visible")&&(s.debug("Showing nag",i.animation.show),"fade"==i.animation.show?a.fadeIn(i.duration,i.easing):a.slideDown(i.duration,i.easing))},hide:function(){s.debug("Showing nag",i.animation.hide),"fade"==i.animation.show?a.fadeIn(i.duration,i.easing):a.slideUp(i.duration,i.easing)},onHide:function(){s.debug("Removing nag",i.animation.hide),a.remove(),i.onHide&&i.onHide()},dismiss:function(e){i.storageMethod&&s.storage.set(i.key,i.value),s.hide(),e.stopImmediatePropagation(),e.preventDefault()},should:{show:function(){return i.persist?(s.debug("Persistent nag is set, can show nag"),!0):s.storage.get(i.key)!=i.value.toString()?(s.debug("Stored value is not set, can show nag",s.storage.get(i.key)),!0):(s.debug("Stored value is set, cannot show nag",s.storage.get(i.key)),!1)}},get:{storageOptions:function(){var e={};return i.expires&&(e.expires=i.expires),i.domain&&(e.domain=i.domain),i.path&&(e.path=i.path),e}},clear:function(){s.storage.remove(i.key)},storage:{set:function(e,t){var n=s.get.storageOptions();if("localstorage"==i.storageMethod&&x.localStorage!==C)x.localStorage.setItem(e,t),s.debug("Value stored using local storage",e,t);else if("sessionstorage"==i.storageMethod&&x.sessionStorage!==C)x.sessionStorage.setItem(e,t),s.debug("Value stored using session storage",e,t);else{if(y.cookie===C)return void s.error(l.noCookieStorage);y.cookie(e,t,n),s.debug("Value stored using cookie",e,t,n)}},get:function(e,t){var n;return"localstorage"==i.storageMethod&&x.localStorage!==C?n=x.localStorage.getItem(e):"sessionstorage"==i.storageMethod&&x.sessionStorage!==C?n=x.sessionStorage.getItem(e):y.cookie!==C?n=y.cookie(e):s.error(l.noCookieStorage),"undefined"!=n&&"null"!=n&&n!==C&&null!==n||(n=C),n},remove:function(e){var t=s.get.storageOptions();"localstorage"==i.storageMethod&&x.localStorage!==C?x.localStorage.removeItem(e):"sessionstorage"==i.storageMethod&&x.sessionStorage!==C?x.sessionStorage.removeItem(e):y.cookie!==C?y.removeCookie(e,t):s.error(l.noStorage)}},setting:function(e,t){if(s.debug("Changing setting",e,t),y.isPlainObject(e))y.extend(!0,i,e);else{if(t===C)return i[e];y.isPlainObject(i[e])?y.extend(!0,i[e],t):i[e]=t}},internal:function(e,t){if(y.isPlainObject(e))y.extend(!0,s,e);else{if(t===C)return s[e];s[e]=t}},debug:function(){!i.silent&&i.debug&&(i.performance?s.performance.log(arguments):(s.debug=Function.prototype.bind.call(console.info,console,i.name+":"),s.debug.apply(console,arguments)))},verbose:function(){!i.silent&&i.verbose&&i.debug&&(i.performance?s.performance.log(arguments):(s.verbose=Function.prototype.bind.call(console.info,console,i.name+":"),s.verbose.apply(console,arguments)))},error:function(){i.silent||(s.error=Function.prototype.bind.call(console.error,console,i.name+":"),s.error.apply(console,arguments))},performance:{log:function(e){var t,n;i.performance&&(n=(t=(new Date).getTime())-(g||t),g=t,p.push({Name:e[0],Arguments:[].slice.call(e,1)||"",Element:c,"Execution Time":n})),clearTimeout(s.performance.timer),s.performance.timer=setTimeout(s.performance.display,500)},display:function(){var e=i.name+":",n=0;g=!1,clearTimeout(s.performance.timer),y.each(p,function(e,t){n+=t["Execution Time"]}),e+=" "+n+"ms",m&&(e+=" '"+m+"'"),(console.group!==C||console.table!==C)&&0<p.length&&(console.groupCollapsed(e),console.table?console.table(p):y.each(p,function(e,t){console.log(t.Name+": "+t["Execution Time"]+"ms")}),console.groupEnd()),p=[]}},invoke:function(i,e,t){var o,a,n,r=u;return e=e||b,t=c||t,"string"==typeof i&&r!==C&&(i=i.split(/[\. ]/),o=i.length-1,y.each(i,function(e,t){var n=e!=o?t+i[e+1].charAt(0).toUpperCase()+i[e+1].slice(1):i;if(y.isPlainObject(r[n])&&e!=o)r=r[n];else{if(r[n]!==C)return a=r[n],!1;if(!y.isPlainObject(r[t])||e==o)return r[t]!==C?a=r[t]:s.error(l.method,i),!1;r=r[t]}})),y.isFunction(a)?n=a.apply(t,e):a!==C&&(n=a),y.isArray(f)?f.push(n):f!==C?f=[f,n]:n!==C&&(f=n),a}},v?(u===C&&s.initialize(),s.invoke(h)):(u!==C&&u.invoke("destroy"),s.initialize())}),f!==C?f:this},y.fn.nag.settings={name:"Nag",silent:!1,debug:!1,verbose:!1,performance:!0,namespace:"Nag",persist:!1,displayTime:0,animation:{show:"slide",hide:"slide"},context:!1,detachable:!1,expires:30,domain:!1,path:"/",storageMethod:"cookie",key:"nag",value:"dismiss",error:{noCookieStorage:"$.cookie is not included. A storage solution is required.",noStorage:"Neither $.cookie or store is defined. A storage solution is required for storing state",method:"The method you called is not defined."},className:{bottom:"bottom",fixed:"fixed"},selector:{close:".close.icon"},speed:500,easing:"easeOutQuad",onHide:function(){}},y.extend(y.easing,{easeOutQuad:function(e,t,n,i,o){return-i*(t/=o)*(t-2)+n}})}(jQuery,window,document),function(z,I,M,L){"use strict";I=void 0!==I&&I.Math==Math?I:"undefined"!=typeof self&&self.Math==Math?self:Function("return this")(),z.fn.popup=function(k){var T,e=z(this),A=z(M),R=z(I),P=z("body"),E=e.selector||"",F=(new Date).getTime(),O=[],D=k,q="string"==typeof D,j=[].slice.call(arguments,1);return e.each(function(){var u,c,e,t,n,d,f=z.isPlainObject(k)?z.extend(!0,{},z.fn.popup.settings,k):z.extend({},z.fn.popup.settings),o=f.selector,m=f.className,g=f.error,p=f.metadata,i=f.namespace,a="."+f.namespace,r="module-"+i,h=z(this),s=z(f.context),l=z(f.scrollContext),v=z(f.boundary),b=f.target?z(f.target):h,y=0,x=!1,C=!1,w=this,S=h.data(r);d={initialize:function(){d.debug("Initializing",h),d.createID(),d.bind.events(),!d.exists()&&f.preserve&&d.create(),f.observeChanges&&d.observeChanges(),d.instantiate()},instantiate:function(){d.verbose("Storing instance",d),S=d,h.data(r,S)},observeChanges:function(){"MutationObserver"in I&&((e=new MutationObserver(d.event.documentChanged)).observe(M,{childList:!0,subtree:!0}),d.debug("Setting up mutation observer",e))},refresh:function(){f.popup?u=z(f.popup).eq(0):f.inline&&(u=b.nextAll(o.popup).eq(0),f.popup=u),f.popup?(u.addClass(m.loading),c=d.get.offsetParent(),u.removeClass(m.loading),f.movePopup&&d.has.popup()&&d.get.offsetParent(u)[0]!==c[0]&&(d.debug("Moving popup to the same offset parent as target"),u.detach().appendTo(c))):c=f.inline?d.get.offsetParent(b):d.has.popup()?d.get.offsetParent(u):P,c.is("html")&&c[0]!==P[0]&&(d.debug("Setting page as offset parent"),c=P),d.get.variation()&&d.set.variation()},reposition:function(){d.refresh(),d.set.position()},destroy:function(){d.debug("Destroying previous module"),e&&e.disconnect(),u&&!f.preserve&&d.removePopup(),clearTimeout(d.hideTimer),clearTimeout(d.showTimer),d.unbind.close(),d.unbind.events(),h.removeData(r)},event:{start:function(e){var t=z.isPlainObject(f.delay)?f.delay.show:f.delay;clearTimeout(d.hideTimer),C||(d.showTimer=setTimeout(d.show,t))},end:function(){var e=z.isPlainObject(f.delay)?f.delay.hide:f.delay;clearTimeout(d.showTimer),d.hideTimer=setTimeout(d.hide,e)},touchstart:function(e){C=!0,d.show()},resize:function(){d.is.visible()&&d.set.position()},documentChanged:function(e){[].forEach.call(e,function(e){e.removedNodes&&[].forEach.call(e.removedNodes,function(e){(e==w||0<z(e).find(w).length)&&(d.debug("Element removed from DOM, tearing down events"),d.destroy())})})},hideGracefully:function(e){var t=z(e.target),n=z.contains(M.documentElement,e.target),i=0<t.closest(o.popup).length;e&&!i&&n?(d.debug("Click occurred outside popup hiding popup"),d.hide()):d.debug("Click was inside popup, keeping popup open")}},create:function(){var e=d.get.html(),t=d.get.title(),n=d.get.content();e||n||t?(d.debug("Creating pop-up html"),e||(e=f.templates.popup({title:t,content:n})),u=z("<div/>").addClass(m.popup).data(p.activator,h).html(e),f.inline?(d.verbose("Inserting popup element inline",u),u.insertAfter(h)):(d.verbose("Appending popup element to body",u),u.appendTo(s)),d.refresh(),d.set.variation(),f.hoverable&&d.bind.popup(),f.onCreate.call(u,w)):0!==b.next(o.popup).length?(d.verbose("Pre-existing popup found"),f.inline=!0,f.popup=b.next(o.popup).data(p.activator,h),d.refresh(),f.hoverable&&d.bind.popup()):f.popup?(z(f.popup).data(p.activator,h),d.verbose("Used popup specified in settings"),d.refresh(),f.hoverable&&d.bind.popup()):d.debug("No content specified skipping display",w)},createID:function(){n=(Math.random().toString(16)+"000000000").substr(2,8),t="."+n,d.verbose("Creating unique id for element",n)},toggle:function(){d.debug("Toggling pop-up"),d.is.hidden()?(d.debug("Popup is hidden, showing pop-up"),d.unbind.close(),d.show()):(d.debug("Popup is visible, hiding pop-up"),d.hide())},show:function(e){if(e=e||function(){},d.debug("Showing pop-up",f.transition),d.is.hidden()&&(!d.is.active()||!d.is.dropdown())){if(d.exists()||d.create(),!1===f.onShow.call(u,w))return void d.debug("onShow callback returned false, cancelling popup animation");f.preserve||f.popup||d.refresh(),u&&d.set.position()&&(d.save.conditions(),f.exclusive&&d.hideAll(),d.animate.show(e))}},hide:function(e){if(e=e||function(){},d.is.visible()||d.is.animating()){if(!1===f.onHide.call(u,w))return void d.debug("onHide callback returned false, cancelling popup animation");d.remove.visible(),d.unbind.close(),d.restore.conditions(),d.animate.hide(e)}},hideAll:function(){z(o.popup).filter("."+m.popupVisible).each(function(){z(this).data(p.activator).popup("hide")})},exists:function(){return!!u&&(f.inline||f.popup?d.has.popup():1<=u.closest(s).length)},removePopup:function(){d.has.popup()&&!f.popup&&(d.debug("Removing popup",u),u.remove(),u=L,f.onRemove.call(u,w))},save:{conditions:function(){d.cache={title:h.attr("title")},d.cache.title&&h.removeAttr("title"),d.verbose("Saving original attributes",d.cache.title)}},restore:{conditions:function(){return d.cache&&d.cache.title&&(h.attr("title",d.cache.title),d.verbose("Restoring original attributes",d.cache.title)),!0}},supports:{svg:function(){return"undefined"==typeof SVGGraphicsElement}},animate:{show:function(e){e=z.isFunction(e)?e:function(){},f.transition&&z.fn.transition!==L&&h.transition("is supported")?(d.set.visible(),u.transition({animation:f.transition+" in",queue:!1,debug:f.debug,verbose:f.verbose,duration:f.duration,onComplete:function(){d.bind.close(),e.call(u,w),f.onVisible.call(u,w)}})):d.error(g.noTransition)},hide:function(e){e=z.isFunction(e)?e:function(){},d.debug("Hiding pop-up"),!1!==f.onHide.call(u,w)?f.transition&&z.fn.transition!==L&&h.transition("is supported")?u.transition({animation:f.transition+" out",queue:!1,duration:f.duration,debug:f.debug,verbose:f.verbose,onComplete:function(){d.reset(),e.call(u,w),f.onHidden.call(u,w)}}):d.error(g.noTransition):d.debug("onHide callback returned false, cancelling popup animation")}},change:{content:function(e){u.html(e)}},get:{html:function(){return h.removeData(p.html),h.data(p.html)||f.html},title:function(){return h.removeData(p.title),h.data(p.title)||f.title},content:function(){return h.removeData(p.content),h.data(p.content)||f.content||h.attr("title")},variation:function(){return h.removeData(p.variation),h.data(p.variation)||f.variation},popup:function(){return u},popupOffset:function(){return u.offset()},calculations:function(){var e,t=d.get.offsetParent(u),n=b[0],i=v[0]==I,o=f.inline||f.popup&&f.movePopup?b.position():b.offset(),a=i?{top:0,left:0}:v.offset(),r={},s=i?{top:R.scrollTop(),left:R.scrollLeft()}:{top:0,left:0};if(r={target:{element:b[0],width:b.outerWidth(),height:b.outerHeight(),top:o.top,left:o.left,margin:{}},popup:{width:u.outerWidth(),height:u.outerHeight()},parent:{width:c.outerWidth(),height:c.outerHeight()},screen:{top:a.top,left:a.left,scroll:{top:s.top,left:s.left},width:v.width(),height:v.height()}},t.get(0)!==c.get(0)){var l=t.offset();r.target.top-=l.top,r.target.left-=l.left,r.parent.width=t.outerWidth(),r.parent.height=t.outerHeight()}return f.setFluidWidth&&d.is.fluid()&&(r.container={width:u.parent().outerWidth()},r.popup.width=r.container.width),r.target.margin.top=f.inline?parseInt(I.getComputedStyle(n).getPropertyValue("margin-top"),10):0,r.target.margin.left=f.inline?d.is.rtl()?parseInt(I.getComputedStyle(n).getPropertyValue("margin-right"),10):parseInt(I.getComputedStyle(n).getPropertyValue("margin-left"),10):0,e=r.screen,r.boundary={top:e.top+e.scroll.top,bottom:e.top+e.scroll.top+e.height,left:e.left+e.scroll.left,right:e.left+e.scroll.left+e.width},r},id:function(){return n},startEvent:function(){return"hover"==f.on?"mouseenter":"focus"==f.on&&"focus"},scrollEvent:function(){return"scroll"},endEvent:function(){return"hover"==f.on?"mouseleave":"focus"==f.on&&"blur"},distanceFromBoundary:function(e,t){var n,i,o={};return n=(t=t||d.get.calculations()).popup,i=t.boundary,e&&(o={top:e.top-i.top,left:e.left-i.left,right:i.right-(e.left+n.width),bottom:i.bottom-(e.top+n.height)},d.verbose("Distance from boundaries determined",e,o)),o},offsetParent:function(e){var t=(e!==L?e[0]:b[0]).parentNode,n=z(t);if(t)for(var i="none"===n.css("transform"),o="static"===n.css("position"),a=n.is("body");t&&!a&&o&&i;)t=t.parentNode,i="none"===(n=z(t)).css("transform"),o="static"===n.css("position"),a=n.is("body");return n&&0<n.length?n:z()},positions:function(){return{"top left":!1,"top center":!1,"top right":!1,"bottom left":!1,"bottom center":!1,"bottom right":!1,"left center":!1,"right center":!1}},nextPosition:function(e){var t=e.split(" "),n=t[0],i=t[1],o="top"==n||"bottom"==n,a=!1,r=!1,s=!1;return x||(d.verbose("All available positions available"),x=d.get.positions()),d.debug("Recording last position tried",e),x[e]=!0,"opposite"===f.prefer&&(s=(s=[{top:"bottom",bottom:"top",left:"right",right:"left"}[n],i]).join(" "),a=!0===x[s],d.debug("Trying opposite strategy",s)),"adjacent"===f.prefer&&o&&(s=(s=[n,{left:"center",center:"right",right:"left"}[i]]).join(" "),r=!0===x[s],d.debug("Trying adjacent strategy",s)),(r||a)&&(d.debug("Using backup position",s),s={"top left":"top center","top center":"top right","top right":"right center","right center":"bottom right","bottom right":"bottom center","bottom center":"bottom left","bottom left":"left center","left center":"top left"}[e]),s}},set:{position:function(e,t){if(0!==b.length&&0!==u.length){var n,i,o,a,r,s,l,c;if(t=t||d.get.calculations(),e=e||h.data(p.position)||f.position,n=h.data(p.offset)||f.offset,i=f.distanceAway,o=t.target,a=t.popup,r=t.parent,d.should.centerArrow(t)&&(d.verbose("Adjusting offset to center arrow on small target element"),"top left"!=e&&"bottom left"!=e||(n+=o.width/2,n-=f.arrowPixelsFromEdge),"top right"!=e&&"bottom right"!=e||(n-=o.width/2,n+=f.arrowPixelsFromEdge)),0===o.width&&0===o.height&&!d.is.svg(o.element))return d.debug("Popup target is hidden, no action taken"),!1;switch(f.inline&&(d.debug("Adding margin to calculation",o.margin),"left center"==e||"right center"==e?(n+=o.margin.top,i+=-o.margin.left):"top left"==e||"top center"==e||"top right"==e?(n+=o.margin.left,i-=o.margin.top):(n+=o.margin.left,i+=o.margin.top)),d.debug("Determining popup position from calculations",e,t),d.is.rtl()&&(e=e.replace(/left|right/g,function(e){return"left"==e?"right":"left"}),d.debug("RTL: Popup position updated",e)),y==f.maxSearchDepth&&"string"==typeof f.lastResort&&(e=f.lastResort),e){case"top left":s={top:"auto",bottom:r.height-o.top+i,left:o.left+n,right:"auto"};break;case"top center":s={bottom:r.height-o.top+i,left:o.left+o.width/2-a.width/2+n,top:"auto",right:"auto"};break;case"top right":s={bottom:r.height-o.top+i,right:r.width-o.left-o.width-n,top:"auto",left:"auto"};break;case"left center":s={top:o.top+o.height/2-a.height/2+n,right:r.width-o.left+i,left:"auto",bottom:"auto"};break;case"right center":s={top:o.top+o.height/2-a.height/2+n,left:o.left+o.width+i,bottom:"auto",right:"auto"};break;case"bottom left":s={top:o.top+o.height+i,left:o.left+n,bottom:"auto",right:"auto"};break;case"bottom center":s={top:o.top+o.height+i,left:o.left+o.width/2-a.width/2+n,bottom:"auto",right:"auto"};break;case"bottom right":s={top:o.top+o.height+i,right:r.width-o.left-o.width-n,left:"auto",bottom:"auto"}}if(s===L&&d.error(g.invalidPosition,e),d.debug("Calculated popup positioning values",s),u.css(s).removeClass(m.position).addClass(e).addClass(m.loading),l=d.get.popupOffset(),c=d.get.distanceFromBoundary(l,t),d.is.offstage(c,e)){if(d.debug("Position is outside viewport",e),y<f.maxSearchDepth)return y++,e=d.get.nextPosition(e),d.debug("Trying new position",e),!!u&&d.set.position(e,t);if(!f.lastResort)return d.debug("Popup could not find a position to display",u),d.error(g.cannotPlace,w),d.remove.attempts(),d.remove.loading(),d.reset(),f.onUnplaceable.call(u,w),!1;d.debug("No position found, showing with last position")}return d.debug("Position is on stage",e),d.remove.attempts(),d.remove.loading(),f.setFluidWidth&&d.is.fluid()&&d.set.fluidWidth(t),!0}d.error(g.notFound)},fluidWidth:function(e){e=e||d.get.calculations(),d.debug("Automatically setting element width to parent width",e.parent.width),u.css("width",e.container.width)},variation:function(e){(e=e||d.get.variation())&&d.has.popup()&&(d.verbose("Adding variation to popup",e),u.addClass(e))},visible:function(){h.addClass(m.visible)}},remove:{loading:function(){u.removeClass(m.loading)},variation:function(e){(e=e||d.get.variation())&&(d.verbose("Removing variation",e),u.removeClass(e))},visible:function(){h.removeClass(m.visible)},attempts:function(){d.verbose("Resetting all searched positions"),y=0,x=!1}},bind:{events:function(){d.debug("Binding popup events to module"),"click"==f.on&&h.on("click"+a,d.toggle),"hover"==f.on&&h.on("touchstart"+a,d.event.touchstart),d.get.startEvent()&&h.on(d.get.startEvent()+a,d.event.start).on(d.get.endEvent()+a,d.event.end),f.target&&d.debug("Target set to element",b),R.on("resize"+t,d.event.resize)},popup:function(){d.verbose("Allowing hover events on popup to prevent closing"),u&&d.has.popup()&&u.on("mouseenter"+a,d.event.start).on("mouseleave"+a,d.event.end)},close:function(){(!0===f.hideOnScroll||"auto"==f.hideOnScroll&&"click"!=f.on)&&d.bind.closeOnScroll(),d.is.closable()?d.bind.clickaway():"hover"==f.on&&C&&d.bind.touchClose()},closeOnScroll:function(){d.verbose("Binding scroll close event to document"),l.one(d.get.scrollEvent()+t,d.event.hideGracefully)},touchClose:function(){d.verbose("Binding popup touchclose event to document"),A.on("touchstart"+t,function(e){d.verbose("Touched away from popup"),d.event.hideGracefully.call(w,e)})},clickaway:function(){d.verbose("Binding popup close event to document"),A.on("click"+t,function(e){d.verbose("Clicked away from popup"),d.event.hideGracefully.call(w,e)})}},unbind:{events:function(){R.off(t),h.off(a)},close:function(){A.off(t),l.off(t)}},has:{popup:function(){return u&&0<u.length}},should:{centerArrow:function(e){return!d.is.basic()&&e.target.width<=2*f.arrowPixelsFromEdge}},is:{closable:function(){return"auto"==f.closable?"hover"!=f.on:f.closable},offstage:function(e,n){var i=[];return z.each(e,function(e,t){t<-f.jitter&&(d.debug("Position exceeds allowable distance from edge",e,t,n),i.push(e))}),0<i.length},svg:function(e){return d.supports.svg()&&e instanceof SVGGraphicsElement},basic:function(){return h.hasClass(m.basic)},active:function(){return h.hasClass(m.active)},animating:function(){return u!==L&&u.hasClass(m.animating)},fluid:function(){return u!==L&&u.hasClass(m.fluid)},visible:function(){return u!==L&&u.hasClass(m.popupVisible)},dropdown:function(){return h.hasClass(m.dropdown)},hidden:function(){return!d.is.visible()},rtl:function(){return"rtl"==h.css("direction")}},reset:function(){d.remove.visible(),f.preserve?z.fn.transition!==L&&u.transition("remove transition"):d.removePopup()},setting:function(e,t){if(z.isPlainObject(e))z.extend(!0,f,e);else{if(t===L)return f[e];f[e]=t}},internal:function(e,t){if(z.isPlainObject(e))z.extend(!0,d,e);else{if(t===L)return d[e];d[e]=t}},debug:function(){!f.silent&&f.debug&&(f.performance?d.performance.log(arguments):(d.debug=Function.prototype.bind.call(console.info,console,f.name+":"),d.debug.apply(console,arguments)))},verbose:function(){!f.silent&&f.verbose&&f.debug&&(f.performance?d.performance.log(arguments):(d.verbose=Function.prototype.bind.call(console.info,console,f.name+":"),d.verbose.apply(console,arguments)))},error:function(){f.silent||(d.error=Function.prototype.bind.call(console.error,console,f.name+":"),d.error.apply(console,arguments))},performance:{log:function(e){var t,n;f.performance&&(n=(t=(new Date).getTime())-(F||t),F=t,O.push({Name:e[0],Arguments:[].slice.call(e,1)||"",Element:w,"Execution Time":n})),clearTimeout(d.performance.timer),d.performance.timer=setTimeout(d.performance.display,500)},display:function(){var e=f.name+":",n=0;F=!1,clearTimeout(d.performance.timer),z.each(O,function(e,t){n+=t["Execution Time"]}),e+=" "+n+"ms",E&&(e+=" '"+E+"'"),(console.group!==L||console.table!==L)&&0<O.length&&(console.groupCollapsed(e),console.table?console.table(O):z.each(O,function(e,t){console.log(t.Name+": "+t["Execution Time"]+"ms")}),console.groupEnd()),O=[]}},invoke:function(i,e,t){var o,a,n,r=S;return e=e||j,t=w||t,"string"==typeof i&&r!==L&&(i=i.split(/[\. ]/),o=i.length-1,z.each(i,function(e,t){var n=e!=o?t+i[e+1].charAt(0).toUpperCase()+i[e+1].slice(1):i;if(z.isPlainObject(r[n])&&e!=o)r=r[n];else{if(r[n]!==L)return a=r[n],!1;if(!z.isPlainObject(r[t])||e==o)return r[t]!==L&&(a=r[t]),!1;r=r[t]}})),z.isFunction(a)?n=a.apply(t,e):a!==L&&(n=a),z.isArray(T)?T.push(n):T!==L?T=[T,n]:n!==L&&(T=n),a}},q?(S===L&&d.initialize(),d.invoke(D)):(S!==L&&S.invoke("destroy"),d.initialize())}),T!==L?T:this},z.fn.popup.settings={name:"Popup",silent:!1,debug:!1,verbose:!1,performance:!0,namespace:"popup",observeChanges:!0,onCreate:function(){},onRemove:function(){},onShow:function(){},onVisible:function(){},onHide:function(){},onUnplaceable:function(){},onHidden:function(){},on:"hover",boundary:I,addTouchEvents:!0,position:"top left",variation:"",movePopup:!0,target:!1,popup:!1,inline:!1,preserve:!1,hoverable:!1,content:!1,html:!1,title:!1,closable:!0,hideOnScroll:"auto",exclusive:!1,context:"body",scrollContext:I,prefer:"opposite",lastResort:!1,arrowPixelsFromEdge:20,delay:{show:50,hide:70},setFluidWidth:!0,duration:200,transition:"scale",distanceAway:0,jitter:2,offset:0,maxSearchDepth:15,error:{invalidPosition:"The position you specified is not a valid position",cannotPlace:"Popup does not fit within the boundaries of the viewport",method:"The method you called is not defined.",noTransition:"This module requires ui transitions <https://github.com/Semantic-Org/UI-Transition>",notFound:"The target or popup you specified does not exist on the page"},metadata:{activator:"activator",content:"content",html:"html",offset:"offset",position:"position",title:"title",variation:"variation"},className:{active:"active",basic:"basic",animating:"animating",dropdown:"dropdown",fluid:"fluid",loading:"loading",popup:"ui popup",position:"top left center bottom right",visible:"visible",popupVisible:"visible"},selector:{popup:".ui.popup"},templates:{escape:function(e){var t={"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;","'":"&#x27;","`":"&#x60;"};return/[&<>"'`]/.test(e)?e.replace(/[&<>"'`]/g,function(e){return t[e]}):e},popup:function(e){var t="",n=z.fn.popup.settings.templates.escape;return typeof e!==L&&(typeof e.title!==L&&e.title&&(e.title=n(e.title),t+='<div class="header">'+e.title+"</div>"),typeof e.content!==L&&e.content&&(e.content=n(e.content),t+='<div class="content">'+e.content+"</div>")),t}}}}(jQuery,window,document),function(k,e,T,A){"use strict";void 0!==(e=void 0!==e&&e.Math==Math?e:"undefined"!=typeof self&&self.Math==Math?self:Function("return this")())&&e.Math==Math||("undefined"!=typeof self&&self.Math==Math?self:Function("return this")());k.fn.progress=function(h){var v,e=k(this),b=e.selector||"",y=(new Date).getTime(),x=[],C=h,w="string"==typeof C,S=[].slice.call(arguments,1);return e.each(function(){var s,i=k.isPlainObject(h)?k.extend(!0,{},k.fn.progress.settings,h):k.extend({},k.fn.progress.settings),t=i.className,n=i.metadata,e=i.namespace,o=i.selector,l=i.error,a="."+e,r="module-"+e,c=k(this),u=k(this).find(o.bar),d=k(this).find(o.progress),f=k(this).find(o.label),m=this,g=c.data(r),p=!1;s={initialize:function(){s.debug("Initializing progress bar",i),s.set.duration(),s.set.transitionEvent(),s.read.metadata(),s.read.settings(),s.instantiate()},instantiate:function(){s.verbose("Storing instance of progress",s),g=s,c.data(r,s)},destroy:function(){s.verbose("Destroying previous progress for",c),clearInterval(g.interval),s.remove.state(),c.removeData(r),g=A},reset:function(){s.remove.nextValue(),s.update.progress(0)},complete:function(){(s.percent===A||s.percent<100)&&(s.remove.progressPoll(),s.set.percent(100))},read:{metadata:function(){var e={percent:c.data(n.percent),total:c.data(n.total),value:c.data(n.value)};e.percent&&(s.debug("Current percent value set from metadata",e.percent),s.set.percent(e.percent)),e.total&&(s.debug("Total value set from metadata",e.total),s.set.total(e.total)),e.value&&(s.debug("Current value set from metadata",e.value),s.set.value(e.value),s.set.progress(e.value))},settings:function(){!1!==i.total&&(s.debug("Current total set in settings",i.total),s.set.total(i.total)),!1!==i.value&&(s.debug("Current value set in settings",i.value),s.set.value(i.value),s.set.progress(s.value)),!1!==i.percent&&(s.debug("Current percent set in settings",i.percent),s.set.percent(i.percent))}},bind:{transitionEnd:function(t){var e=s.get.transitionEnd();u.one(e+a,function(e){clearTimeout(s.failSafeTimer),t.call(this,e)}),s.failSafeTimer=setTimeout(function(){u.triggerHandler(e)},i.duration+i.failSafeDelay),s.verbose("Adding fail safe timer",s.timer)}},increment:function(e){var t,n;s.has.total()?n=(t=s.get.value())+(e=e||1):(n=(t=s.get.percent())+(e=e||s.get.randomValue()),100,s.debug("Incrementing percentage by",t,n)),n=s.get.normalizedValue(n),s.set.progress(n)},decrement:function(e){var t,n;s.get.total()?(n=(t=s.get.value())-(e=e||1),s.debug("Decrementing value by",e,t)):(n=(t=s.get.percent())-(e=e||s.get.randomValue()),s.debug("Decrementing percentage by",e,t)),n=s.get.normalizedValue(n),s.set.progress(n)},has:{progressPoll:function(){return s.progressPoll},total:function(){return!1!==s.get.total()}},get:{text:function(e){var t=s.value||0,n=s.total||0,i=p?s.get.displayPercent():s.percent||0,o=0<s.total?n-t:100-i;return e=(e=e||"").replace("{value}",t).replace("{total}",n).replace("{left}",o).replace("{percent}",i),s.verbose("Adding variables to progress bar text",e),e},normalizedValue:function(e){if(e<0)return s.debug("Value cannot decrement below 0"),0;if(s.has.total()){if(e>s.total)return s.debug("Value cannot increment above total",s.total),s.total}else if(100<e)return s.debug("Value cannot increment above 100 percent"),100;return e},updateInterval:function(){return"auto"==i.updateInterval?i.duration:i.updateInterval},randomValue:function(){return s.debug("Generating random increment percentage"),Math.floor(Math.random()*i.random.max+i.random.min)},numericValue:function(e){return"string"==typeof e?""!==e.replace(/[^\d.]/g,"")&&+e.replace(/[^\d.]/g,""):e},transitionEnd:function(){var e,t=T.createElement("element"),n={transition:"transitionend",OTransition:"oTransitionEnd",MozTransition:"transitionend",WebkitTransition:"webkitTransitionEnd"};for(e in n)if(t.style[e]!==A)return n[e]},displayPercent:function(){var e=u.width(),t=c.width(),n=parseInt(u.css("min-width"),10)<e?e/t*100:s.percent;return 0<i.precision?Math.round(n*(10*i.precision))/(10*i.precision):Math.round(n)},percent:function(){return s.percent||0},value:function(){return s.nextValue||s.value||0},total:function(){return s.total||!1}},create:{progressPoll:function(){s.progressPoll=setTimeout(function(){s.update.toNextValue(),s.remove.progressPoll()},s.get.updateInterval())}},is:{complete:function(){return s.is.success()||s.is.warning()||s.is.error()},success:function(){return c.hasClass(t.success)},warning:function(){return c.hasClass(t.warning)},error:function(){return c.hasClass(t.error)},active:function(){return c.hasClass(t.active)},visible:function(){return c.is(":visible")}},remove:{progressPoll:function(){s.verbose("Removing progress poll timer"),s.progressPoll&&(clearTimeout(s.progressPoll),delete s.progressPoll)},nextValue:function(){s.verbose("Removing progress value stored for next update"),delete s.nextValue},state:function(){s.verbose("Removing stored state"),delete s.total,delete s.percent,delete s.value},active:function(){s.verbose("Removing active state"),c.removeClass(t.active)},success:function(){s.verbose("Removing success state"),c.removeClass(t.success)},warning:function(){s.verbose("Removing warning state"),c.removeClass(t.warning)},error:function(){s.verbose("Removing error state"),c.removeClass(t.error)}},set:{barWidth:function(e){100<e?s.error(l.tooHigh,e):e<0?s.error(l.tooLow,e):(u.css("width",e+"%"),c.attr("data-percent",parseInt(e,10)))},duration:function(e){e="number"==typeof(e=e||i.duration)?e+"ms":e,s.verbose("Setting progress bar transition duration",e),u.css({"transition-duration":e})},percent:function(e){e="string"==typeof e?+e.replace("%",""):e,e=0<i.precision?Math.round(e*(10*i.precision))/(10*i.precision):Math.round(e),s.percent=e,s.has.total()||(s.value=0<i.precision?Math.round(e/100*s.total*(10*i.precision))/(10*i.precision):Math.round(e/100*s.total*10)/10,i.limitValues&&(s.value=100<s.value?100:s.value<0?0:s.value)),s.set.barWidth(e),s.set.labelInterval(),s.set.labels(),i.onChange.call(m,e,s.value,s.total)},labelInterval:function(){clearInterval(s.interval),s.bind.transitionEnd(function(){s.verbose("Bar finished animating, removing continuous label updates"),clearInterval(s.interval),p=!1,s.set.labels()}),p=!0,s.interval=setInterval(function(){k.contains(T.documentElement,m)||(clearInterval(s.interval),p=!1),s.set.labels()},i.framerate)},labels:function(){s.verbose("Setting both bar progress and outer label text"),s.set.barLabel(),s.set.state()},label:function(e){(e=e||"")&&(e=s.get.text(e),s.verbose("Setting label to text",e),f.text(e))},state:function(e){100===(e=e!==A?e:s.percent)?i.autoSuccess&&!(s.is.warning()||s.is.error()||s.is.success())?(s.set.success(),s.debug("Automatically triggering success at 100%")):(s.verbose("Reached 100% removing active state"),s.remove.active(),s.remove.progressPoll()):0<e?(s.verbose("Adjusting active progress bar label",e),s.set.active()):(s.remove.active(),s.set.label(i.text.active))},barLabel:function(e){e!==A?d.text(s.get.text(e)):"ratio"==i.label&&s.total?(s.verbose("Adding ratio to bar label"),d.text(s.get.text(i.text.ratio))):"percent"==i.label&&(s.verbose("Adding percentage to bar label"),d.text(s.get.text(i.text.percent)))},active:function(e){e=e||i.text.active,s.debug("Setting active state"),i.showActivity&&!s.is.active()&&c.addClass(t.active),s.remove.warning(),s.remove.error(),s.remove.success(),(e=i.onLabelUpdate("active",e,s.value,s.total))&&s.set.label(e),s.bind.transitionEnd(function(){i.onActive.call(m,s.value,s.total)})},success:function(e){e=e||i.text.success||i.text.active,s.debug("Setting success state"),c.addClass(t.success),s.remove.active(),s.remove.warning(),s.remove.error(),s.complete(),e=i.text.success?i.onLabelUpdate("success",e,s.value,s.total):i.onLabelUpdate("active",e,s.value,s.total),s.set.label(e),s.bind.transitionEnd(function(){i.onSuccess.call(m,s.total)})},warning:function(e){e=e||i.text.warning,s.debug("Setting warning state"),c.addClass(t.warning),s.remove.active(),s.remove.success(),s.remove.error(),s.complete(),(e=i.onLabelUpdate("warning",e,s.value,s.total))&&s.set.label(e),s.bind.transitionEnd(function(){i.onWarning.call(m,s.value,s.total)})},error:function(e){e=e||i.text.error,s.debug("Setting error state"),c.addClass(t.error),s.remove.active(),s.remove.success(),s.remove.warning(),s.complete(),(e=i.onLabelUpdate("error",e,s.value,s.total))&&s.set.label(e),s.bind.transitionEnd(function(){i.onError.call(m,s.value,s.total)})},transitionEvent:function(){s.get.transitionEnd()},total:function(e){s.total=e},value:function(e){s.value=e},progress:function(e){s.has.progressPoll()?(s.debug("Updated within interval, setting next update to use new value",e),s.set.nextValue(e)):(s.debug("First update in progress update interval, immediately updating",e),s.update.progress(e),s.create.progressPoll())},nextValue:function(e){s.nextValue=e}},update:{toNextValue:function(){var e=s.nextValue;e&&(s.debug("Update interval complete using last updated value",e),s.update.progress(e),s.remove.nextValue())},progress:function(e){var t;!1===(e=s.get.numericValue(e))&&s.error(l.nonNumeric,e),e=s.get.normalizedValue(e),s.has.total()?(s.set.value(e),t=e/s.total*100,s.debug("Calculating percent complete from total",t)):(t=e,s.debug("Setting value to exact percentage value",t)),s.set.percent(t)}},setting:function(e,t){if(s.debug("Changing setting",e,t),k.isPlainObject(e))k.extend(!0,i,e);else{if(t===A)return i[e];k.isPlainObject(i[e])?k.extend(!0,i[e],t):i[e]=t}},internal:function(e,t){if(k.isPlainObject(e))k.extend(!0,s,e);else{if(t===A)return s[e];s[e]=t}},debug:function(){!i.silent&&i.debug&&(i.performance?s.performance.log(arguments):(s.debug=Function.prototype.bind.call(console.info,console,i.name+":"),s.debug.apply(console,arguments)))},verbose:function(){!i.silent&&i.verbose&&i.debug&&(i.performance?s.performance.log(arguments):(s.verbose=Function.prototype.bind.call(console.info,console,i.name+":"),s.verbose.apply(console,arguments)))},error:function(){i.silent||(s.error=Function.prototype.bind.call(console.error,console,i.name+":"),s.error.apply(console,arguments))},performance:{log:function(e){var t,n;i.performance&&(n=(t=(new Date).getTime())-(y||t),y=t,x.push({Name:e[0],Arguments:[].slice.call(e,1)||"",Element:m,"Execution Time":n})),clearTimeout(s.performance.timer),s.performance.timer=setTimeout(s.performance.display,500)},display:function(){var e=i.name+":",n=0;y=!1,clearTimeout(s.performance.timer),k.each(x,function(e,t){n+=t["Execution Time"]}),e+=" "+n+"ms",b&&(e+=" '"+b+"'"),(console.group!==A||console.table!==A)&&0<x.length&&(console.groupCollapsed(e),console.table?console.table(x):k.each(x,function(e,t){console.log(t.Name+": "+t["Execution Time"]+"ms")}),console.groupEnd()),x=[]}},invoke:function(i,e,t){var o,a,n,r=g;return e=e||S,t=m||t,"string"==typeof i&&r!==A&&(i=i.split(/[\. ]/),o=i.length-1,k.each(i,function(e,t){var n=e!=o?t+i[e+1].charAt(0).toUpperCase()+i[e+1].slice(1):i;if(k.isPlainObject(r[n])&&e!=o)r=r[n];else{if(r[n]!==A)return a=r[n],!1;if(!k.isPlainObject(r[t])||e==o)return r[t]!==A?a=r[t]:s.error(l.method,i),!1;r=r[t]}})),k.isFunction(a)?n=a.apply(t,e):a!==A&&(n=a),k.isArray(v)?v.push(n):v!==A?v=[v,n]:n!==A&&(v=n),a}},w?(g===A&&s.initialize(),s.invoke(C)):(g!==A&&g.invoke("destroy"),s.initialize())}),v!==A?v:this},k.fn.progress.settings={name:"Progress",namespace:"progress",silent:!1,debug:!1,verbose:!1,performance:!0,random:{min:2,max:5},duration:300,updateInterval:"auto",autoSuccess:!0,showActivity:!0,limitValues:!0,label:"percent",precision:0,framerate:1e3/30,percent:!1,total:!1,value:!1,failSafeDelay:100,onLabelUpdate:function(e,t,n,i){return t},onChange:function(e,t,n){},onSuccess:function(e){},onActive:function(e,t){},onError:function(e,t){},onWarning:function(e,t){},error:{method:"The method you called is not defined.",nonNumeric:"Progress value is non numeric",tooHigh:"Value specified is above 100%",tooLow:"Value specified is below 0%"},regExp:{variable:/\{\$*[A-z0-9]+\}/g},metadata:{percent:"percent",total:"total",value:"value"},selector:{bar:"> .bar",label:"> .label",progress:".bar > .progress"},text:{active:!1,error:!1,success:!1,warning:!1,percent:"{percent}%",ratio:"{value} of {total}"},className:{active:"active",error:"error",success:"success",warning:"warning"}}}(jQuery,window,document),function(w,e,t,S){"use strict";e=void 0!==e&&e.Math==Math?e:"undefined"!=typeof self&&self.Math==Math?self:Function("return this")(),w.fn.rating=function(m){var g,p=w(this),h=p.selector||"",v=(new Date).getTime(),b=[],y=m,x="string"==typeof y,C=[].slice.call(arguments,1);return p.each(function(){var e,i,o=w.isPlainObject(m)?w.extend(!0,{},w.fn.rating.settings,m):w.extend({},w.fn.rating.settings),t=o.namespace,a=o.className,n=o.metadata,r=o.selector,s=(o.error,"."+t),l="module-"+t,c=this,u=w(this).data(l),d=w(this),f=d.find(r.icon);i={initialize:function(){i.verbose("Initializing rating module",o),0===f.length&&i.setup.layout(),o.interactive?i.enable():i.disable(),i.set.initialLoad(),i.set.rating(i.get.initialRating()),i.remove.initialLoad(),i.instantiate()},instantiate:function(){i.verbose("Instantiating module",o),u=i,d.data(l,i)},destroy:function(){i.verbose("Destroying previous instance",u),i.remove.events(),d.removeData(l)},refresh:function(){f=d.find(r.icon)},setup:{layout:function(){var e=i.get.maxRating(),t=w.fn.rating.settings.templates.icon(e);i.debug("Generating icon html dynamically"),d.html(t),i.refresh()}},event:{mouseenter:function(){var e=w(this);e.nextAll().removeClass(a.selected),d.addClass(a.selected),e.addClass(a.selected).prevAll().addClass(a.selected)},mouseleave:function(){d.removeClass(a.selected),f.removeClass(a.selected)},click:function(){var e=w(this),t=i.get.rating(),n=f.index(e)+1;("auto"==o.clearable?1===f.length:o.clearable)&&t==n?i.clearRating():i.set.rating(n)}},clearRating:function(){i.debug("Clearing current rating"),i.set.rating(0)},bind:{events:function(){i.verbose("Binding events"),d.on("mouseenter"+s,r.icon,i.event.mouseenter).on("mouseleave"+s,r.icon,i.event.mouseleave).on("click"+s,r.icon,i.event.click)}},remove:{events:function(){i.verbose("Removing events"),d.off(s)},initialLoad:function(){e=!1}},enable:function(){i.debug("Setting rating to interactive mode"),i.bind.events(),d.removeClass(a.disabled)},disable:function(){i.debug("Setting rating to read-only mode"),i.remove.events(),d.addClass(a.disabled)},is:{initialLoad:function(){return e}},get:{initialRating:function(){return d.data(n.rating)!==S?(d.removeData(n.rating),d.data(n.rating)):o.initialRating},maxRating:function(){return d.data(n.maxRating)!==S?(d.removeData(n.maxRating),d.data(n.maxRating)):o.maxRating},rating:function(){var e=f.filter("."+a.active).length;return i.verbose("Current rating retrieved",e),e}},set:{rating:function(e){var t=0<=e-1?e-1:0,n=f.eq(t);d.removeClass(a.selected),f.removeClass(a.selected).removeClass(a.active),0<e&&(i.verbose("Setting current rating to",e),n.prevAll().addBack().addClass(a.active)),i.is.initialLoad()||o.onRate.call(c,e)},initialLoad:function(){e=!0}},setting:function(e,t){if(i.debug("Changing setting",e,t),w.isPlainObject(e))w.extend(!0,o,e);else{if(t===S)return o[e];w.isPlainObject(o[e])?w.extend(!0,o[e],t):o[e]=t}},internal:function(e,t){if(w.isPlainObject(e))w.extend(!0,i,e);else{if(t===S)return i[e];i[e]=t}},debug:function(){!o.silent&&o.debug&&(o.performance?i.performance.log(arguments):(i.debug=Function.prototype.bind.call(console.info,console,o.name+":"),i.debug.apply(console,arguments)))},verbose:function(){!o.silent&&o.verbose&&o.debug&&(o.performance?i.performance.log(arguments):(i.verbose=Function.prototype.bind.call(console.info,console,o.name+":"),i.verbose.apply(console,arguments)))},error:function(){o.silent||(i.error=Function.prototype.bind.call(console.error,console,o.name+":"),i.error.apply(console,arguments))},performance:{log:function(e){var t,n;o.performance&&(n=(t=(new Date).getTime())-(v||t),v=t,b.push({Name:e[0],Arguments:[].slice.call(e,1)||"",Element:c,"Execution Time":n})),clearTimeout(i.performance.timer),i.performance.timer=setTimeout(i.performance.display,500)},display:function(){var e=o.name+":",n=0;v=!1,clearTimeout(i.performance.timer),w.each(b,function(e,t){n+=t["Execution Time"]}),e+=" "+n+"ms",h&&(e+=" '"+h+"'"),1<p.length&&(e+=" ("+p.length+")"),(console.group!==S||console.table!==S)&&0<b.length&&(console.groupCollapsed(e),console.table?console.table(b):w.each(b,function(e,t){console.log(t.Name+": "+t["Execution Time"]+"ms")}),console.groupEnd()),b=[]}},invoke:function(i,e,t){var o,a,n,r=u;return e=e||C,t=c||t,"string"==typeof i&&r!==S&&(i=i.split(/[\. ]/),o=i.length-1,w.each(i,function(e,t){var n=e!=o?t+i[e+1].charAt(0).toUpperCase()+i[e+1].slice(1):i;if(w.isPlainObject(r[n])&&e!=o)r=r[n];else{if(r[n]!==S)return a=r[n],!1;if(!w.isPlainObject(r[t])||e==o)return r[t]!==S&&(a=r[t]),!1;r=r[t]}})),w.isFunction(a)?n=a.apply(t,e):a!==S&&(n=a),w.isArray(g)?g.push(n):g!==S?g=[g,n]:n!==S&&(g=n),a}},x?(u===S&&i.initialize(),i.invoke(y)):(u!==S&&u.invoke("destroy"),i.initialize())}),g!==S?g:this},w.fn.rating.settings={name:"Rating",namespace:"rating",slent:!1,debug:!1,verbose:!1,performance:!0,initialRating:0,interactive:!0,maxRating:4,clearable:"auto",fireOnInit:!1,onRate:function(e){},error:{method:"The method you called is not defined",noMaximum:"No maximum rating specified. Cannot generate HTML automatically"},metadata:{rating:"rating",maxRating:"maxRating"},className:{active:"active",disabled:"disabled",selected:"selected",loading:"loading"},selector:{icon:".icon"},templates:{icon:function(e){for(var t=1,n="";t<=e;)n+='<i class="icon"></i>',t++;return n}}}}(jQuery,window,document),function(E,F,O,D){"use strict";F=void 0!==F&&F.Math==Math?F:"undefined"!=typeof self&&self.Math==Math?self:Function("return this")(),E.fn.search=function(l){var C,w=E(this),S=w.selector||"",k=(new Date).getTime(),T=[],A=l,R="string"==typeof A,P=[].slice.call(arguments,1);return E(this).each(function(){var f,c=E.isPlainObject(l)?E.extend(!0,{},E.fn.search.settings,l):E.extend({},E.fn.search.settings),m=c.className,u=c.metadata,d=c.regExp,a=c.fields,g=c.selector,p=c.error,e=c.namespace,i="."+e,t=e+"-module",h=E(this),v=h.find(g.prompt),n=h.find(g.searchButton),o=h.find(g.results),r=h.find(g.result),b=(h.find(g.category),this),s=h.data(t),y=!1,x=!1;f={initialize:function(){f.verbose("Initializing module"),f.get.settings(),f.determine.searchFields(),f.bind.events(),f.set.type(),f.create.results(),f.instantiate()},instantiate:function(){f.verbose("Storing instance of module",f),s=f,h.data(t,f)},destroy:function(){f.verbose("Destroying instance"),h.off(i).removeData(t)},refresh:function(){f.debug("Refreshing selector cache"),v=h.find(g.prompt),n=h.find(g.searchButton),h.find(g.category),o=h.find(g.results),r=h.find(g.result)},refreshResults:function(){o=h.find(g.results),r=h.find(g.result)},bind:{events:function(){f.verbose("Binding events to search"),c.automatic&&(h.on(f.get.inputEvent()+i,g.prompt,f.event.input),v.attr("autocomplete","off")),h.on("focus"+i,g.prompt,f.event.focus).on("blur"+i,g.prompt,f.event.blur).on("keydown"+i,g.prompt,f.handleKeyboard).on("click"+i,g.searchButton,f.query).on("mousedown"+i,g.results,f.event.result.mousedown).on("mouseup"+i,g.results,f.event.result.mouseup).on("click"+i,g.result,f.event.result.click)}},determine:{searchFields:function(){l&&l.searchFields!==D&&(c.searchFields=l.searchFields)}},event:{input:function(){c.searchDelay?(clearTimeout(f.timer),f.timer=setTimeout(function(){f.is.focused()&&f.query()},c.searchDelay)):f.query()},focus:function(){f.set.focus(),c.searchOnFocus&&f.has.minimumCharacters()&&f.query(function(){f.can.show()&&f.showResults()})},blur:function(e){var t=O.activeElement===this,n=function(){f.cancel.query(),f.remove.focus(),f.timer=setTimeout(f.hideResults,c.hideDelay)};t||(x=!1,f.resultsClicked?(f.debug("Determining if user action caused search to close"),h.one("click.close"+i,g.results,function(e){f.is.inMessage(e)||y?v.focus():(y=!1,f.is.animating()||f.is.hidden()||n())})):(f.debug("Input blurred without user action, closing results"),n()))},result:{mousedown:function(){f.resultsClicked=!0},mouseup:function(){f.resultsClicked=!1},click:function(e){f.debug("Search result selected");var t=E(this),n=t.find(g.title).eq(0),i=t.is("a[href]")?t:t.find("a[href]").eq(0),o=i.attr("href")||!1,a=i.attr("target")||!1,r=(n.html(),0<n.length&&n.text()),s=f.get.results(),l=t.data(u.result)||f.get.result(r,s);if(E.isFunction(c.onSelect)&&!1===c.onSelect.call(b,l,s))return f.debug("Custom onSelect callback cancelled default select action"),void(y=!0);f.hideResults(),r&&f.set.value(r),o&&(f.verbose("Opening search link found in result",i),"_blank"==a||e.ctrlKey?F.open(o):F.location.href=o)}}},handleKeyboard:function(e){var t,n=h.find(g.result),i=h.find(g.category),o=n.filter("."+m.active),a=n.index(o),r=n.length,s=0<o.length,l=e.which,c=13,u=38,d=40;if(l==27&&(f.verbose("Escape key pressed, blurring search field"),f.hideResults(),x=!0),f.is.visible())if(l==c){if(f.verbose("Enter key pressed, selecting active result"),0<n.filter("."+m.active).length)return f.event.result.click.call(n.filter("."+m.active),e),e.preventDefault(),!1}else l==u&&s?(f.verbose("Up key pressed, changing active result"),t=a-1<0?a:a-1,i.removeClass(m.active),n.removeClass(m.active).eq(t).addClass(m.active).closest(i).addClass(m.active),e.preventDefault()):l==d&&(f.verbose("Down key pressed, changing active result"),t=r<=a+1?a:a+1,i.removeClass(m.active),n.removeClass(m.active).eq(t).addClass(m.active).closest(i).addClass(m.active),e.preventDefault());else l==c&&(f.verbose("Enter key pressed, executing query"),f.query(),f.set.buttonPressed(),v.one("keyup",f.remove.buttonFocus))},setup:{api:function(t,n){var e={debug:c.debug,on:!1,cache:c.cache,action:"search",urlData:{query:t},onSuccess:function(e){f.parse.response.call(b,e,t),n()},onFailure:function(){f.displayMessage(p.serverError),n()},onAbort:function(e){},onError:f.error};E.extend(!0,e,c.apiSettings),f.verbose("Setting up API request",e),h.api(e)}},can:{useAPI:function(){return E.fn.api!==D},show:function(){return f.is.focused()&&!f.is.visible()&&!f.is.empty()},transition:function(){return c.transition&&E.fn.transition!==D&&h.transition("is supported")}},is:{animating:function(){return o.hasClass(m.animating)},hidden:function(){return o.hasClass(m.hidden)},inMessage:function(e){if(e.target){var t=E(e.target);return E.contains(O.documentElement,e.target)&&0<t.closest(g.message).length}},empty:function(){return""===o.html()},visible:function(){return 0<o.filter(":visible").length},focused:function(){return 0<v.filter(":focus").length}},get:{settings:function(){E.isPlainObject(l)&&l.searchFullText&&(c.fullTextSearch=l.searchFullText,f.error(c.error.oldSearchSyntax,b))},inputEvent:function(){var e=v[0];return e!==D&&e.oninput!==D?"input":e!==D&&e.onpropertychange!==D?"propertychange":"keyup"},value:function(){return v.val()},results:function(){return h.data(u.results)},result:function(n,e){var i=["title","id"],o=!1;return n=n!==D?n:f.get.value(),e=e!==D?e:f.get.results(),"category"===c.type?(f.debug("Finding result that matches",n),E.each(e,function(e,t){if(E.isArray(t.results)&&(o=f.search.object(n,t.results,i)[0]))return!1})):(f.debug("Finding result in results object",n),o=f.search.object(n,e,i)[0]),o||!1}},select:{firstResult:function(){f.verbose("Selecting first result"),r.first().addClass(m.active)}},set:{focus:function(){h.addClass(m.focus)},loading:function(){h.addClass(m.loading)},value:function(e){f.verbose("Setting search input value",e),v.val(e)},type:function(e){e=e||c.type,"category"==c.type&&h.addClass(c.type)},buttonPressed:function(){n.addClass(m.pressed)}},remove:{loading:function(){h.removeClass(m.loading)},focus:function(){h.removeClass(m.focus)},buttonPressed:function(){n.removeClass(m.pressed)}},query:function(e){e=E.isFunction(e)?e:function(){};var t=f.get.value(),n=f.read.cache(t);e=e||function(){},f.has.minimumCharacters()?(n?(f.debug("Reading result from cache",t),f.save.results(n.results),f.addResults(n.html),f.inject.id(n.results),e()):(f.debug("Querying for",t),E.isPlainObject(c.source)||E.isArray(c.source)?(f.search.local(t),e()):f.can.useAPI()?f.search.remote(t,e):(f.error(p.source),e())),c.onSearchQuery.call(b,t)):f.hideResults()},search:{local:function(e){var t,n=f.search.object(e,c.content);f.set.loading(),f.save.results(n),f.debug("Returned full local search results",n),0<c.maxResults&&(f.debug("Using specified max results",n),n=n.slice(0,c.maxResults)),"category"==c.type&&(n=f.create.categoryResults(n)),t=f.generateResults({results:n}),f.remove.loading(),f.addResults(t),f.inject.id(n),f.write.cache(e,{html:t,results:n})},remote:function(e,t){t=E.isFunction(t)?t:function(){},h.api("is loading")&&h.api("abort"),f.setup.api(e,t),h.api("query")},object:function(i,t,e){var a=[],r=[],s=[],n=i.toString().replace(d.escape,"\\$&"),o=new RegExp(d.beginsWith+n,"i"),l=function(e,t){var n=-1==E.inArray(t,a),i=-1==E.inArray(t,s),o=-1==E.inArray(t,r);n&&i&&o&&e.push(t)};return t=t||c.source,e=e!==D?e:c.searchFields,E.isArray(e)||(e=[e]),t===D||!1===t?(f.error(p.source),[]):(E.each(e,function(e,n){E.each(t,function(e,t){"string"==typeof t[n]&&(-1!==t[n].search(o)?l(a,t):"exact"===c.fullTextSearch&&f.exactSearch(i,t[n])?l(r,t):1==c.fullTextSearch&&f.fuzzySearch(i,t[n])&&l(s,t))})}),E.merge(r,s),E.merge(a,r),a)}},exactSearch:function(e,t){return e=e.toLowerCase(),-1<(t=t.toLowerCase()).indexOf(e)},fuzzySearch:function(e,t){var n=t.length,i=e.length;if("string"!=typeof e)return!1;if(e=e.toLowerCase(),t=t.toLowerCase(),n<i)return!1;if(i===n)return e===t;e:for(var o=0,a=0;o<i;o++){for(var r=e.charCodeAt(o);a<n;)if(t.charCodeAt(a++)===r)continue e;return!1}return!0},parse:{response:function(e,t){var n=f.generateResults(e);f.verbose("Parsing server response",e),e!==D&&t!==D&&e[a.results]!==D&&(f.addResults(n),f.inject.id(e[a.results]),f.write.cache(t,{html:n,results:e[a.results]}),f.save.results(e[a.results]))}},cancel:{query:function(){f.can.useAPI()&&h.api("abort")}},has:{minimumCharacters:function(){return f.get.value().length>=c.minCharacters},results:function(){return 0!==o.length&&""!=o.html()}},clear:{cache:function(e){var t=h.data(u.cache);e?e&&t&&t[e]&&(f.debug("Removing value from cache",e),delete t[e],h.data(u.cache,t)):(f.debug("Clearing cache",e),h.removeData(u.cache))}},read:{cache:function(e){var t=h.data(u.cache);return!!c.cache&&(f.verbose("Checking cache for generated html for query",e),"object"==typeof t&&t[e]!==D&&t[e])}},create:{categoryResults:function(e){var n={};return E.each(e,function(e,t){t.category&&(n[t.category]===D?(f.verbose("Creating new category of results",t.category),n[t.category]={name:t.category,results:[t]}):n[t.category].results.push(t))}),n},id:function(e,t){var n,i=e+1;return t!==D?(n=String.fromCharCode(97+t)+i,f.verbose("Creating category result id",n)):(n=i,f.verbose("Creating result id",n)),n},results:function(){0===o.length&&(o=E("<div />").addClass(m.results).appendTo(h))}},inject:{result:function(e,t,n){f.verbose("Injecting result into results");var i=n!==D?o.children().eq(n).children(g.results).first().children(g.result).eq(t):o.children(g.result).eq(t);f.verbose("Injecting results metadata",i),i.data(u.result,e)},id:function(i){f.debug("Injecting unique ids into results");var o=0,a=0;return"category"===c.type?E.each(i,function(e,i){a=0,E.each(i.results,function(e,t){var n=i.results[e];n.id===D&&(n.id=f.create.id(a,o)),f.inject.result(n,a,o),a++}),o++}):E.each(i,function(e,t){var n=i[e];n.id===D&&(n.id=f.create.id(a)),f.inject.result(n,a),a++}),i}},save:{results:function(e){f.verbose("Saving current search results to metadata",e),h.data(u.results,e)}},write:{cache:function(e,t){var n=h.data(u.cache)!==D?h.data(u.cache):{};c.cache&&(f.verbose("Writing generated html to cache",e,t),n[e]=t,h.data(u.cache,n))}},addResults:function(e){if(E.isFunction(c.onResultsAdd)&&!1===c.onResultsAdd.call(o,e))return f.debug("onResultsAdd callback cancelled default action"),!1;e?(o.html(e),f.refreshResults(),c.selectFirstResult&&f.select.firstResult(),f.showResults()):f.hideResults(function(){o.empty()})},showResults:function(e){e=E.isFunction(e)?e:function(){},x||!f.is.visible()&&f.has.results()&&(f.can.transition()?(f.debug("Showing results with css animations"),o.transition({animation:c.transition+" in",debug:c.debug,verbose:c.verbose,duration:c.duration,onComplete:function(){e()},queue:!0})):(f.debug("Showing results with javascript"),o.stop().fadeIn(c.duration,c.easing)),c.onResultsOpen.call(o))},hideResults:function(e){e=E.isFunction(e)?e:function(){},f.is.visible()&&(f.can.transition()?(f.debug("Hiding results with css animations"),o.transition({animation:c.transition+" out",debug:c.debug,verbose:c.verbose,duration:c.duration,onComplete:function(){e()},queue:!0})):(f.debug("Hiding results with javascript"),o.stop().fadeOut(c.duration,c.easing)),c.onResultsClose.call(o))},generateResults:function(e){f.debug("Generating html from response",e);var t=c.templates[c.type],n=E.isPlainObject(e[a.results])&&!E.isEmptyObject(e[a.results]),i=E.isArray(e[a.results])&&0<e[a.results].length,o="";return n||i?(0<c.maxResults&&(n?"standard"==c.type&&f.error(p.maxResults):e[a.results]=e[a.results].slice(0,c.maxResults)),E.isFunction(t)?o=t(e,a):f.error(p.noTemplate,!1)):c.showNoResults&&(o=f.displayMessage(p.noResults,"empty")),c.onResults.call(b,e),o},displayMessage:function(e,t){return t=t||"standard",f.debug("Displaying message",e,t),f.addResults(c.templates.message(e,t)),c.templates.message(e,t)},setting:function(e,t){if(E.isPlainObject(e))E.extend(!0,c,e);else{if(t===D)return c[e];c[e]=t}},internal:function(e,t){if(E.isPlainObject(e))E.extend(!0,f,e);else{if(t===D)return f[e];f[e]=t}},debug:function(){!c.silent&&c.debug&&(c.performance?f.performance.log(arguments):(f.debug=Function.prototype.bind.call(console.info,console,c.name+":"),f.debug.apply(console,arguments)))},verbose:function(){!c.silent&&c.verbose&&c.debug&&(c.performance?f.performance.log(arguments):(f.verbose=Function.prototype.bind.call(console.info,console,c.name+":"),f.verbose.apply(console,arguments)))},error:function(){c.silent||(f.error=Function.prototype.bind.call(console.error,console,c.name+":"),f.error.apply(console,arguments))},performance:{log:function(e){var t,n;c.performance&&(n=(t=(new Date).getTime())-(k||t),k=t,T.push({Name:e[0],Arguments:[].slice.call(e,1)||"",Element:b,"Execution Time":n})),clearTimeout(f.performance.timer),f.performance.timer=setTimeout(f.performance.display,500)},display:function(){var e=c.name+":",n=0;k=!1,clearTimeout(f.performance.timer),E.each(T,function(e,t){n+=t["Execution Time"]}),e+=" "+n+"ms",S&&(e+=" '"+S+"'"),1<w.length&&(e+=" ("+w.length+")"),(console.group!==D||console.table!==D)&&0<T.length&&(console.groupCollapsed(e),console.table?console.table(T):E.each(T,function(e,t){console.log(t.Name+": "+t["Execution Time"]+"ms")}),console.groupEnd()),T=[]}},invoke:function(i,e,t){var o,a,n,r=s;return e=e||P,t=b||t,"string"==typeof i&&r!==D&&(i=i.split(/[\. ]/),o=i.length-1,E.each(i,function(e,t){var n=e!=o?t+i[e+1].charAt(0).toUpperCase()+i[e+1].slice(1):i;if(E.isPlainObject(r[n])&&e!=o)r=r[n];else{if(r[n]!==D)return a=r[n],!1;if(!E.isPlainObject(r[t])||e==o)return r[t]!==D&&(a=r[t]),!1;r=r[t]}})),E.isFunction(a)?n=a.apply(t,e):a!==D&&(n=a),E.isArray(C)?C.push(n):C!==D?C=[C,n]:n!==D&&(C=n),a}},R?(s===D&&f.initialize(),f.invoke(A)):(s!==D&&s.invoke("destroy"),f.initialize())}),C!==D?C:this},E.fn.search.settings={name:"Search",namespace:"search",silent:!1,debug:!1,verbose:!1,performance:!0,type:"standard",minCharacters:1,selectFirstResult:!1,apiSettings:!1,source:!1,searchOnFocus:!0,searchFields:["title","description"],displayField:"",fullTextSearch:"exact",automatic:!0,hideDelay:0,searchDelay:200,maxResults:7,cache:!0,showNoResults:!0,transition:"scale",duration:200,easing:"easeOutExpo",onSelect:!1,onResultsAdd:!1,onSearchQuery:function(e){},onResults:function(e){},onResultsOpen:function(){},onResultsClose:function(){},className:{animating:"animating",active:"active",empty:"empty",focus:"focus",hidden:"hidden",loading:"loading",results:"results",pressed:"down"},error:{source:"Cannot search. No source used, and Semantic API module was not included",noResults:"Your search returned no results",logging:"Error in debug logging, exiting.",noEndpoint:"No search endpoint was specified",noTemplate:"A valid template name was not specified.",oldSearchSyntax:"searchFullText setting has been renamed fullTextSearch for consistency, please adjust your settings.",serverError:"There was an issue querying the server.",maxResults:"Results must be an array to use maxResults setting",method:"The method you called is not defined."},metadata:{cache:"cache",results:"results",result:"result"},regExp:{escape:/[\-\[\]\/\{\}\(\)\*\+\?\.\\\^\$\|]/g,beginsWith:"(?:s|^)"},fields:{categories:"results",categoryName:"name",categoryResults:"results",description:"description",image:"image",price:"price",results:"results",title:"title",url:"url",action:"action",actionText:"text",actionURL:"url"},selector:{prompt:".prompt",searchButton:".search.button",results:".results",message:".results > .message",category:".category",result:".result",title:".title, .name"},templates:{escape:function(e){var t={"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;","'":"&#x27;","`":"&#x60;"};return/[&<>"'`]/.test(e)?e.replace(/[&<>"'`]/g,function(e){return t[e]}):e},message:function(e,t){var n="";return e!==D&&t!==D&&(n+='<div class="message '+t+'">',n+="empty"==t?'<div class="header">No Results</div class="header"><div class="description">'+e+'</div class="description">':' <div class="description">'+e+"</div>",n+="</div>"),n},category:function(e,n){var i="";E.fn.search.settings.templates.escape;return e[n.categoryResults]!==D&&(E.each(e[n.categoryResults],function(e,t){t[n.results]!==D&&0<t.results.length&&(i+='<div class="category">',t[n.categoryName]!==D&&(i+='<div class="name">'+t[n.categoryName]+"</div>"),i+='<div class="results">',E.each(t.results,function(e,t){t[n.url]?i+='<a class="result" href="'+t[n.url]+'">':i+='<a class="result">',t[n.image]!==D&&(i+='<div class="image"> <img src="'+t[n.image]+'"></div>'),i+='<div class="content">',t[n.price]!==D&&(i+='<div class="price">'+t[n.price]+"</div>"),t[n.title]!==D&&(i+='<div class="title">'+t[n.title]+"</div>"),t[n.description]!==D&&(i+='<div class="description">'+t[n.description]+"</div>"),i+="</div>",i+="</a>"}),i+="</div>",i+="</div>")}),e[n.action]&&(i+='<a href="'+e[n.action][n.actionURL]+'" class="action">'+e[n.action][n.actionText]+"</a>"),i)},standard:function(e,n){var i="";return e[n.results]!==D&&(E.each(e[n.results],function(e,t){t[n.url]?i+='<a class="result" href="'+t[n.url]+'">':i+='<a class="result">',t[n.image]!==D&&(i+='<div class="image"> <img src="'+t[n.image]+'"></div>'),i+='<div class="content">',t[n.price]!==D&&(i+='<div class="price">'+t[n.price]+"</div>"),t[n.title]!==D&&(i+='<div class="title">'+t[n.title]+"</div>"),t[n.description]!==D&&(i+='<div class="description">'+t[n.description]+"</div>"),i+="</div>",i+="</a>"}),e[n.action]&&(i+='<a href="'+e[n.action][n.actionURL]+'" class="action">'+e[n.action][n.actionText]+"</a>"),i)}}}}(jQuery,window,document),function(A,e,R,P){"use strict";e=void 0!==e&&e.Math==Math?e:"undefined"!=typeof self&&self.Math==Math?self:Function("return this")(),A.fn.shape=function(v){var b,y=A(this),x=(A("body"),(new Date).getTime()),C=[],w=v,S="string"==typeof w,k=[].slice.call(arguments,1),T=e.requestAnimationFrame||e.mozRequestAnimationFrame||e.webkitRequestAnimationFrame||e.msRequestAnimationFrame||function(e){setTimeout(e,0)};return y.each(function(){var i,o,a,t=y.selector||"",r=A.isPlainObject(v)?A.extend(!0,{},A.fn.shape.settings,v):A.extend({},A.fn.shape.settings),e=r.namespace,s=r.selector,n=r.error,l=r.className,c="."+e,u="module-"+e,d=A(this),f=d.find(s.sides),m=d.find(s.side),g=!1,p=this,h=d.data(u);a={initialize:function(){a.verbose("Initializing module for",p),a.set.defaultSide(),a.instantiate()},instantiate:function(){a.verbose("Storing instance of module",a),h=a,d.data(u,h)},destroy:function(){a.verbose("Destroying previous module for",p),d.removeData(u).off(c)},refresh:function(){a.verbose("Refreshing selector cache for",p),d=A(p),f=A(this).find(s.shape),m=A(this).find(s.side)},repaint:function(){a.verbose("Forcing repaint event");(f[0]||R.createElement("div")).offsetWidth},animate:function(e,t){a.verbose("Animating box with properties",e),t=t||function(e){a.verbose("Executing animation callback"),e!==P&&e.stopPropagation(),a.reset(),a.set.active()},r.beforeChange.call(o[0]),a.get.transitionEvent()?(a.verbose("Starting CSS animation"),d.addClass(l.animating),f.css(e).one(a.get.transitionEvent(),t),a.set.duration(r.duration),T(function(){d.addClass(l.animating),i.addClass(l.hidden)})):t()},queue:function(e){a.debug("Queueing animation of",e),f.one(a.get.transitionEvent(),function(){a.debug("Executing queued animation"),setTimeout(function(){d.shape(e)},0)})},reset:function(){a.verbose("Animating states reset"),d.removeClass(l.animating).attr("style","").removeAttr("style"),f.attr("style","").removeAttr("style"),m.attr("style","").removeAttr("style").removeClass(l.hidden),o.removeClass(l.animating).attr("style","").removeAttr("style")},is:{complete:function(){return m.filter("."+l.active)[0]==o[0]},animating:function(){return d.hasClass(l.animating)}},set:{defaultSide:function(){i=d.find("."+r.className.active),o=0<i.next(s.side).length?i.next(s.side):d.find(s.side).first(),g=!1,a.verbose("Active side set to",i),a.verbose("Next side set to",o)},duration:function(e){e="number"==typeof(e=e||r.duration)?e+"ms":e,a.verbose("Setting animation duration",e),(r.duration||0===r.duration)&&f.add(m).css({"-webkit-transition-duration":e,"-moz-transition-duration":e,"-ms-transition-duration":e,"-o-transition-duration":e,"transition-duration":e})},currentStageSize:function(){var e=d.find("."+r.className.active),t=e.outerWidth(!0),n=e.outerHeight(!0);d.css({width:t,height:n})},stageSize:function(){var e=d.clone().addClass(l.loading),t=e.find("."+r.className.active),n=g?e.find(s.side).eq(g):0<t.next(s.side).length?t.next(s.side):e.find(s.side).first(),i="next"==r.width?n.outerWidth(!0):"initial"==r.width?d.width():r.width,o="next"==r.height?n.outerHeight(!0):"initial"==r.height?d.height():r.height;t.removeClass(l.active),n.addClass(l.active),e.insertAfter(d),e.remove(),"auto"!=r.width&&(d.css("width",i+r.jitter),a.verbose("Specifying width during animation",i)),"auto"!=r.height&&(d.css("height",o+r.jitter),a.verbose("Specifying height during animation",o))},nextSide:function(e){g=e,o=m.filter(e),g=m.index(o),0===o.length&&(a.set.defaultSide(),a.error(n.side)),a.verbose("Next side manually set to",o)},active:function(){a.verbose("Setting new side to active",o),m.removeClass(l.active),o.addClass(l.active),r.onChange.call(o[0]),a.set.defaultSide()}},flip:{up:function(){if(!a.is.complete()||a.is.animating()||r.allowRepeats)if(a.is.animating())a.queue("flip up");else{a.debug("Flipping up",o);var e=a.get.transform.up();a.set.stageSize(),a.stage.above(),a.animate(e)}else a.debug("Side already visible",o)},down:function(){if(!a.is.complete()||a.is.animating()||r.allowRepeats)if(a.is.animating())a.queue("flip down");else{a.debug("Flipping down",o);var e=a.get.transform.down();a.set.stageSize(),a.stage.below(),a.animate(e)}else a.debug("Side already visible",o)},left:function(){if(!a.is.complete()||a.is.animating()||r.allowRepeats)if(a.is.animating())a.queue("flip left");else{a.debug("Flipping left",o);var e=a.get.transform.left();a.set.stageSize(),a.stage.left(),a.animate(e)}else a.debug("Side already visible",o)},right:function(){if(!a.is.complete()||a.is.animating()||r.allowRepeats)if(a.is.animating())a.queue("flip right");else{a.debug("Flipping right",o);var e=a.get.transform.right();a.set.stageSize(),a.stage.right(),a.animate(e)}else a.debug("Side already visible",o)},over:function(){!a.is.complete()||a.is.animating()||r.allowRepeats?a.is.animating()?a.queue("flip over"):(a.debug("Flipping over",o),a.set.stageSize(),a.stage.behind(),a.animate(a.get.transform.over())):a.debug("Side already visible",o)},back:function(){!a.is.complete()||a.is.animating()||r.allowRepeats?a.is.animating()?a.queue("flip back"):(a.debug("Flipping back",o),a.set.stageSize(),a.stage.behind(),a.animate(a.get.transform.back())):a.debug("Side already visible",o)}},get:{transform:{up:function(){return{transform:"translateY("+-(i.outerHeight(!0)-o.outerHeight(!0))/2+"px) translateZ("+-i.outerHeight(!0)/2+"px) rotateX(-90deg)"}},down:function(){return{transform:"translateY("+-(i.outerHeight(!0)-o.outerHeight(!0))/2+"px) translateZ("+-i.outerHeight(!0)/2+"px) rotateX(90deg)"}},left:function(){return{transform:"translateX("+-(i.outerWidth(!0)-o.outerWidth(!0))/2+"px) translateZ("+-i.outerWidth(!0)/2+"px) rotateY(90deg)"}},right:function(){return{transform:"translateX("+-(i.outerWidth(!0)-o.outerWidth(!0))/2+"px) translateZ("+-i.outerWidth(!0)/2+"px) rotateY(-90deg)"}},over:function(){return{transform:"translateX("+-(i.outerWidth(!0)-o.outerWidth(!0))/2+"px) rotateY(180deg)"}},back:function(){return{transform:"translateX("+-(i.outerWidth(!0)-o.outerWidth(!0))/2+"px) rotateY(-180deg)"}}},transitionEvent:function(){var e,t=R.createElement("element"),n={transition:"transitionend",OTransition:"oTransitionEnd",MozTransition:"transitionend",WebkitTransition:"webkitTransitionEnd"};for(e in n)if(t.style[e]!==P)return n[e]},nextSide:function(){return 0<i.next(s.side).length?i.next(s.side):d.find(s.side).first()}},stage:{above:function(){var e={origin:(i.outerHeight(!0)-o.outerHeight(!0))/2,depth:{active:o.outerHeight(!0)/2,next:i.outerHeight(!0)/2}};a.verbose("Setting the initial animation position as above",o,e),f.css({transform:"translateZ(-"+e.depth.active+"px)"}),i.css({transform:"rotateY(0deg) translateZ("+e.depth.active+"px)"}),o.addClass(l.animating).css({top:e.origin+"px",transform:"rotateX(90deg) translateZ("+e.depth.next+"px)"})},below:function(){var e={origin:(i.outerHeight(!0)-o.outerHeight(!0))/2,depth:{active:o.outerHeight(!0)/2,next:i.outerHeight(!0)/2}};a.verbose("Setting the initial animation position as below",o,e),f.css({transform:"translateZ(-"+e.depth.active+"px)"}),i.css({transform:"rotateY(0deg) translateZ("+e.depth.active+"px)"}),o.addClass(l.animating).css({top:e.origin+"px",transform:"rotateX(-90deg) translateZ("+e.depth.next+"px)"})},left:function(){var e=i.outerWidth(!0),t=o.outerWidth(!0),n={origin:(e-t)/2,depth:{active:t/2,next:e/2}};a.verbose("Setting the initial animation position as left",o,n),f.css({transform:"translateZ(-"+n.depth.active+"px)"}),i.css({transform:"rotateY(0deg) translateZ("+n.depth.active+"px)"}),o.addClass(l.animating).css({left:n.origin+"px",transform:"rotateY(-90deg) translateZ("+n.depth.next+"px)"})},right:function(){var e=i.outerWidth(!0),t=o.outerWidth(!0),n={origin:(e-t)/2,depth:{active:t/2,next:e/2}};a.verbose("Setting the initial animation position as left",o,n),f.css({transform:"translateZ(-"+n.depth.active+"px)"}),i.css({transform:"rotateY(0deg) translateZ("+n.depth.active+"px)"}),o.addClass(l.animating).css({left:n.origin+"px",transform:"rotateY(90deg) translateZ("+n.depth.next+"px)"})},behind:function(){var e=i.outerWidth(!0),t=o.outerWidth(!0),n={origin:(e-t)/2,depth:{active:t/2,next:e/2}};a.verbose("Setting the initial animation position as behind",o,n),i.css({transform:"rotateY(0deg)"}),o.addClass(l.animating).css({left:n.origin+"px",transform:"rotateY(-180deg)"})}},setting:function(e,t){if(a.debug("Changing setting",e,t),A.isPlainObject(e))A.extend(!0,r,e);else{if(t===P)return r[e];A.isPlainObject(r[e])?A.extend(!0,r[e],t):r[e]=t}},internal:function(e,t){if(A.isPlainObject(e))A.extend(!0,a,e);else{if(t===P)return a[e];a[e]=t}},debug:function(){!r.silent&&r.debug&&(r.performance?a.performance.log(arguments):(a.debug=Function.prototype.bind.call(console.info,console,r.name+":"),a.debug.apply(console,arguments)))},verbose:function(){!r.silent&&r.verbose&&r.debug&&(r.performance?a.performance.log(arguments):(a.verbose=Function.prototype.bind.call(console.info,console,r.name+":"),a.verbose.apply(console,arguments)))},error:function(){r.silent||(a.error=Function.prototype.bind.call(console.error,console,r.name+":"),a.error.apply(console,arguments))},performance:{log:function(e){var t,n;r.performance&&(n=(t=(new Date).getTime())-(x||t),x=t,C.push({Name:e[0],Arguments:[].slice.call(e,1)||"",Element:p,"Execution Time":n})),clearTimeout(a.performance.timer),a.performance.timer=setTimeout(a.performance.display,500)},display:function(){var e=r.name+":",n=0;x=!1,clearTimeout(a.performance.timer),A.each(C,function(e,t){n+=t["Execution Time"]}),e+=" "+n+"ms",t&&(e+=" '"+t+"'"),1<y.length&&(e+=" ("+y.length+")"),(console.group!==P||console.table!==P)&&0<C.length&&(console.groupCollapsed(e),console.table?console.table(C):A.each(C,function(e,t){console.log(t.Name+": "+t["Execution Time"]+"ms")}),console.groupEnd()),C=[]}},invoke:function(i,e,t){var o,a,n,r=h;return e=e||k,t=p||t,"string"==typeof i&&r!==P&&(i=i.split(/[\. ]/),o=i.length-1,A.each(i,function(e,t){var n=e!=o?t+i[e+1].charAt(0).toUpperCase()+i[e+1].slice(1):i;if(A.isPlainObject(r[n])&&e!=o)r=r[n];else{if(r[n]!==P)return a=r[n],!1;if(!A.isPlainObject(r[t])||e==o)return r[t]!==P&&(a=r[t]),!1;r=r[t]}})),A.isFunction(a)?n=a.apply(t,e):a!==P&&(n=a),A.isArray(b)?b.push(n):b!==P?b=[b,n]:n!==P&&(b=n),a}},S?(h===P&&a.initialize(),a.invoke(w)):(h!==P&&h.invoke("destroy"),a.initialize())}),b!==P?b:this},A.fn.shape.settings={name:"Shape",silent:!1,debug:!1,verbose:!1,jitter:0,performance:!0,namespace:"shape",width:"initial",height:"initial",beforeChange:function(){},onChange:function(){},allowRepeats:!1,duration:!1,error:{side:"You tried to switch to a side that does not exist.",method:"The method you called is not defined"},className:{animating:"animating",hidden:"hidden",loading:"loading",active:"active"},selector:{sides:".sides",side:".side"}}}(jQuery,window,document),function(q,j,z,I){"use strict";j=void 0!==j&&j.Math==Math?j:"undefined"!=typeof self&&self.Math==Math?self:Function("return this")(),q.fn.sidebar=function(x){var C,e=q(this),w=q(j),S=q(z),k=q("html"),T=q("head"),A=e.selector||"",R=(new Date).getTime(),P=[],E=x,F="string"==typeof E,O=[].slice.call(arguments,1),D=j.requestAnimationFrame||j.mozRequestAnimationFrame||j.webkitRequestAnimationFrame||j.msRequestAnimationFrame||function(e){setTimeout(e,0)};return e.each(function(){var r,s,e,t,l,c,u=q.isPlainObject(x)?q.extend(!0,{},q.fn.sidebar.settings,x):q.extend({},q.fn.sidebar.settings),n=u.selector,a=u.className,i=u.namespace,o=u.regExp,d=u.error,f="."+i,m="module-"+i,g=q(this),p=q(u.context),h=g.children(n.sidebar),v=(p.children(n.fixed),p.children(n.pusher)),b=this,y=g.data(m);c={initialize:function(){c.debug("Initializing sidebar",x),c.create.id(),l=c.get.transitionEvent(),u.delaySetup?D(c.setup.layout):c.setup.layout(),D(function(){c.setup.cache()}),c.instantiate()},instantiate:function(){c.verbose("Storing instance of module",c),y=c,g.data(m,c)},create:{id:function(){e=(Math.random().toString(16)+"000000000").substr(2,8),s="."+e,c.verbose("Creating unique id for element",e)}},destroy:function(){c.verbose("Destroying previous module for",g),g.off(f).removeData(m),c.is.ios()&&c.remove.ios(),p.off(s),w.off(s),S.off(s)},event:{clickaway:function(e){var t=0<v.find(e.target).length||v.is(e.target),n=p.is(e.target);t&&(c.verbose("User clicked on dimmed page"),c.hide()),n&&(c.verbose("User clicked on dimmable context (scaled out page)"),c.hide())},touch:function(e){},containScroll:function(e){b.scrollTop<=0&&(b.scrollTop=1),b.scrollTop+b.offsetHeight>=b.scrollHeight&&(b.scrollTop=b.scrollHeight-b.offsetHeight-1)},scroll:function(e){0===q(e.target).closest(n.sidebar).length&&e.preventDefault()}},bind:{clickaway:function(){c.verbose("Adding clickaway events to context",p),u.closable&&p.on("click"+s,c.event.clickaway).on("touchend"+s,c.event.clickaway)},scrollLock:function(){u.scrollLock&&(c.debug("Disabling page scroll"),w.on("DOMMouseScroll"+s,c.event.scroll)),c.verbose("Adding events to contain sidebar scroll"),S.on("touchmove"+s,c.event.touch),g.on("scroll"+f,c.event.containScroll)}},unbind:{clickaway:function(){c.verbose("Removing clickaway events from context",p),p.off(s)},scrollLock:function(){c.verbose("Removing scroll lock from page"),S.off(s),w.off(s),g.off("scroll"+f)}},add:{inlineCSS:function(){var e,t=c.cache.width||g.outerWidth(),n=c.cache.height||g.outerHeight(),i=c.is.rtl(),o=c.get.direction(),a={left:t,right:-t,top:n,bottom:-n};i&&(c.verbose("RTL detected, flipping widths"),a.left=-t,a.right=t),e="<style>","left"===o||"right"===o?(c.debug("Adding CSS rules for animation distance",t),e+=" .ui.visible."+o+".sidebar ~ .fixed, .ui.visible."+o+".sidebar ~ .pusher {   -webkit-transform: translate3d("+a[o]+"px, 0, 0);           transform: translate3d("+a[o]+"px, 0, 0); }"):"top"!==o&&"bottom"!=o||(e+=" .ui.visible."+o+".sidebar ~ .fixed, .ui.visible."+o+".sidebar ~ .pusher {   -webkit-transform: translate3d(0, "+a[o]+"px, 0);           transform: translate3d(0, "+a[o]+"px, 0); }"),c.is.ie()&&("left"===o||"right"===o?(c.debug("Adding CSS rules for animation distance",t),e+=" body.pushable > .ui.visible."+o+".sidebar ~ .pusher:after {   -webkit-transform: translate3d("+a[o]+"px, 0, 0);           transform: translate3d("+a[o]+"px, 0, 0); }"):"top"!==o&&"bottom"!=o||(e+=" body.pushable > .ui.visible."+o+".sidebar ~ .pusher:after {   -webkit-transform: translate3d(0, "+a[o]+"px, 0);           transform: translate3d(0, "+a[o]+"px, 0); }"),e+=" body.pushable > .ui.visible.left.sidebar ~ .ui.visible.right.sidebar ~ .pusher:after, body.pushable > .ui.visible.right.sidebar ~ .ui.visible.left.sidebar ~ .pusher:after {   -webkit-transform: translate3d(0px, 0, 0);           transform: translate3d(0px, 0, 0); }"),r=q(e+="</style>").appendTo(T),c.debug("Adding sizing css to head",r)}},refresh:function(){c.verbose("Refreshing selector cache"),p=q(u.context),h=p.children(n.sidebar),v=p.children(n.pusher),p.children(n.fixed),c.clear.cache()},refreshSidebars:function(){c.verbose("Refreshing other sidebars"),h=p.children(n.sidebar)},repaint:function(){c.verbose("Forcing repaint event"),b.style.display="none";b.offsetHeight;b.scrollTop=b.scrollTop,b.style.display=""},setup:{cache:function(){c.cache={width:g.outerWidth(),height:g.outerHeight(),rtl:"rtl"==g.css("direction")}},layout:function(){0===p.children(n.pusher).length&&(c.debug("Adding wrapper element for sidebar"),c.error(d.pusher),v=q('<div class="pusher" />'),p.children().not(n.omitted).not(h).wrapAll(v),c.refresh()),0!==g.nextAll(n.pusher).length&&g.nextAll(n.pusher)[0]===v[0]||(c.debug("Moved sidebar to correct parent element"),c.error(d.movedSidebar,b),g.detach().prependTo(p),c.refresh()),c.clear.cache(),c.set.pushable(),c.set.direction()}},attachEvents:function(e,t){var n=q(e);t=q.isFunction(c[t])?c[t]:c.toggle,0<n.length?(c.debug("Attaching sidebar events to element",e,t),n.on("click"+f,t)):c.error(d.notFound,e)},show:function(e){if(e=q.isFunction(e)?e:function(){},c.is.hidden()){if(c.refreshSidebars(),u.overlay&&(c.error(d.overlay),u.transition="overlay"),c.refresh(),c.othersActive())if(c.debug("Other sidebars currently visible"),u.exclusive){if("overlay"!=u.transition)return void c.hideOthers(c.show);c.hideOthers()}else u.transition="overlay";c.pushPage(function(){e.call(b),u.onShow.call(b)}),u.onChange.call(b),u.onVisible.call(b)}else c.debug("Sidebar is already visible")},hide:function(e){e=q.isFunction(e)?e:function(){},(c.is.visible()||c.is.animating())&&(c.debug("Hiding sidebar",e),c.refreshSidebars(),c.pullPage(function(){e.call(b),u.onHidden.call(b)}),u.onChange.call(b),u.onHide.call(b))},othersAnimating:function(){return 0<h.not(g).filter("."+a.animating).length},othersVisible:function(){return 0<h.not(g).filter("."+a.visible).length},othersActive:function(){return c.othersVisible()||c.othersAnimating()},hideOthers:function(e){var t=h.not(g).filter("."+a.visible),n=t.length,i=0;e=e||function(){},t.sidebar("hide",function(){++i==n&&e()})},toggle:function(){c.verbose("Determining toggled direction"),c.is.hidden()?c.show():c.hide()},pushPage:function(t){var e,n,i,o=c.get.transition(),a="overlay"===o||c.othersActive()?g:v;t=q.isFunction(t)?t:function(){},"scale down"==u.transition&&c.scrollToTop(),c.set.transition(o),c.repaint(),e=function(){c.bind.clickaway(),c.add.inlineCSS(),c.set.animating(),c.set.visible()},n=function(){c.set.dimmed()},i=function(e){e.target==a[0]&&(a.off(l+s,i),c.remove.animating(),c.bind.scrollLock(),t.call(b))},a.off(l+s),a.on(l+s,i),D(e),u.dimPage&&!c.othersVisible()&&D(n)},pullPage:function(t){var e,n,i=c.get.transition(),o="overlay"==i||c.othersActive()?g:v;t=q.isFunction(t)?t:function(){},c.verbose("Removing context push state",c.get.direction()),c.unbind.clickaway(),c.unbind.scrollLock(),e=function(){c.set.transition(i),c.set.animating(),c.remove.visible(),u.dimPage&&!c.othersVisible()&&v.removeClass(a.dimmed)},n=function(e){e.target==o[0]&&(o.off(l+s,n),c.remove.animating(),c.remove.transition(),c.remove.inlineCSS(),("scale down"==i||u.returnScroll&&c.is.mobile())&&c.scrollBack(),t.call(b))},o.off(l+s),o.on(l+s,n),D(e)},scrollToTop:function(){c.verbose("Scrolling to top of page to avoid animation issues"),t=q(j).scrollTop(),g.scrollTop(0),j.scrollTo(0,0)},scrollBack:function(){c.verbose("Scrolling back to original page position"),j.scrollTo(0,t)},clear:{cache:function(){c.verbose("Clearing cached dimensions"),c.cache={}}},set:{ios:function(){k.addClass(a.ios)},pushed:function(){p.addClass(a.pushed)},pushable:function(){p.addClass(a.pushable)},dimmed:function(){v.addClass(a.dimmed)},active:function(){g.addClass(a.active)},animating:function(){g.addClass(a.animating)},transition:function(e){e=e||c.get.transition(),g.addClass(e)},direction:function(e){e=e||c.get.direction(),g.addClass(a[e])},visible:function(){g.addClass(a.visible)},overlay:function(){g.addClass(a.overlay)}},remove:{inlineCSS:function(){c.debug("Removing inline css styles",r),r&&0<r.length&&r.remove()},ios:function(){k.removeClass(a.ios)},pushed:function(){p.removeClass(a.pushed)},pushable:function(){p.removeClass(a.pushable)},active:function(){g.removeClass(a.active)},animating:function(){g.removeClass(a.animating)},transition:function(e){e=e||c.get.transition(),g.removeClass(e)},direction:function(e){e=e||c.get.direction(),g.removeClass(a[e])},visible:function(){g.removeClass(a.visible)},overlay:function(){g.removeClass(a.overlay)}},get:{direction:function(){return g.hasClass(a.top)?a.top:g.hasClass(a.right)?a.right:g.hasClass(a.bottom)?a.bottom:a.left},transition:function(){var e,t=c.get.direction();return e=c.is.mobile()?"auto"==u.mobileTransition?u.defaultTransition.mobile[t]:u.mobileTransition:"auto"==u.transition?u.defaultTransition.computer[t]:u.transition,c.verbose("Determined transition",e),e},transitionEvent:function(){var e,t=z.createElement("element"),n={transition:"transitionend",OTransition:"oTransitionEnd",MozTransition:"transitionend",WebkitTransition:"webkitTransitionEnd"};for(e in n)if(t.style[e]!==I)return n[e]}},is:{ie:function(){return!j.ActiveXObject&&"ActiveXObject"in j||"ActiveXObject"in j},ios:function(){var e=navigator.userAgent,t=e.match(o.ios),n=e.match(o.mobileChrome);return!(!t||n)&&(c.verbose("Browser was found to be iOS",e),!0)},mobile:function(){var e=navigator.userAgent;return e.match(o.mobile)?(c.verbose("Browser was found to be mobile",e),!0):(c.verbose("Browser is not mobile, using regular transition",e),!1)},hidden:function(){return!c.is.visible()},visible:function(){return g.hasClass(a.visible)},open:function(){return c.is.visible()},closed:function(){return c.is.hidden()},vertical:function(){return g.hasClass(a.top)},animating:function(){return p.hasClass(a.animating)},rtl:function(){return c.cache.rtl===I&&(c.cache.rtl="rtl"==g.css("direction")),c.cache.rtl}},setting:function(e,t){if(c.debug("Changing setting",e,t),q.isPlainObject(e))q.extend(!0,u,e);else{if(t===I)return u[e];q.isPlainObject(u[e])?q.extend(!0,u[e],t):u[e]=t}},internal:function(e,t){if(q.isPlainObject(e))q.extend(!0,c,e);else{if(t===I)return c[e];c[e]=t}},debug:function(){!u.silent&&u.debug&&(u.performance?c.performance.log(arguments):(c.debug=Function.prototype.bind.call(console.info,console,u.name+":"),c.debug.apply(console,arguments)))},verbose:function(){!u.silent&&u.verbose&&u.debug&&(u.performance?c.performance.log(arguments):(c.verbose=Function.prototype.bind.call(console.info,console,u.name+":"),c.verbose.apply(console,arguments)))},error:function(){u.silent||(c.error=Function.prototype.bind.call(console.error,console,u.name+":"),c.error.apply(console,arguments))},performance:{log:function(e){var t,n;u.performance&&(n=(t=(new Date).getTime())-(R||t),R=t,P.push({Name:e[0],Arguments:[].slice.call(e,1)||"",Element:b,"Execution Time":n})),clearTimeout(c.performance.timer),c.performance.timer=setTimeout(c.performance.display,500)},display:function(){var e=u.name+":",n=0;R=!1,clearTimeout(c.performance.timer),q.each(P,function(e,t){n+=t["Execution Time"]}),e+=" "+n+"ms",A&&(e+=" '"+A+"'"),(console.group!==I||console.table!==I)&&0<P.length&&(console.groupCollapsed(e),console.table?console.table(P):q.each(P,function(e,t){console.log(t.Name+": "+t["Execution Time"]+"ms")}),console.groupEnd()),P=[]}},invoke:function(i,e,t){var o,a,n,r=y;return e=e||O,t=b||t,"string"==typeof i&&r!==I&&(i=i.split(/[\. ]/),o=i.length-1,q.each(i,function(e,t){var n=e!=o?t+i[e+1].charAt(0).toUpperCase()+i[e+1].slice(1):i;if(q.isPlainObject(r[n])&&e!=o)r=r[n];else{if(r[n]!==I)return a=r[n],!1;if(!q.isPlainObject(r[t])||e==o)return r[t]!==I?a=r[t]:c.error(d.method,i),!1;r=r[t]}})),q.isFunction(a)?n=a.apply(t,e):a!==I&&(n=a),q.isArray(C)?C.push(n):C!==I?C=[C,n]:n!==I&&(C=n),a}},F?(y===I&&c.initialize(),c.invoke(E)):(y!==I&&c.invoke("destroy"),c.initialize())}),C!==I?C:this},q.fn.sidebar.settings={name:"Sidebar",namespace:"sidebar",silent:!1,debug:!1,verbose:!1,performance:!0,transition:"auto",mobileTransition:"auto",defaultTransition:{computer:{left:"uncover",right:"uncover",top:"overlay",bottom:"overlay"},mobile:{left:"uncover",right:"uncover",top:"overlay",bottom:"overlay"}},context:"body",exclusive:!1,closable:!0,dimPage:!0,scrollLock:!1,returnScroll:!1,delaySetup:!1,duration:500,onChange:function(){},onShow:function(){},onHide:function(){},onHidden:function(){},onVisible:function(){},className:{active:"active",animating:"animating",dimmed:"dimmed",ios:"ios",pushable:"pushable",pushed:"pushed",right:"right",top:"top",left:"left",bottom:"bottom",visible:"visible"},selector:{fixed:".fixed",omitted:"script, link, style, .ui.modal, .ui.dimmer, .ui.nag, .ui.fixed",pusher:".pusher",sidebar:".ui.sidebar"},regExp:{ios:/(iPad|iPhone|iPod)/g,mobileChrome:/(CriOS)/g,mobile:/Mobile|iP(hone|od|ad)|Android|BlackBerry|IEMobile|Kindle|NetFront|Silk-Accelerated|(hpw|web)OS|Fennec|Minimo|Opera M(obi|ini)|Blazer|Dolfin|Dolphin|Skyfire|Zune/g},error:{method:"The method you called is not defined.",pusher:"Had to add pusher element. For optimal performance make sure body content is inside a pusher element",movedSidebar:"Had to move sidebar. For optimal performance make sure sidebar and pusher are direct children of your body tag",overlay:"The overlay setting is no longer supported, use animation: overlay",notFound:"There were no elements that matched the specified selector"}}}(jQuery,window,document),function(T,A,R,P){"use strict";A=void 0!==A&&A.Math==Math?A:"undefined"!=typeof self&&self.Math==Math?self:Function("return this")(),T.fn.sticky=function(v){var b,e=T(this),y=e.selector||"",x=(new Date).getTime(),C=[],w=v,S="string"==typeof w,k=[].slice.call(arguments,1);return e.each(function(){var i,o,e,t,d,f=T.isPlainObject(v)?T.extend(!0,{},T.fn.sticky.settings,v):T.extend({},T.fn.sticky.settings),n=f.className,a=f.namespace,r=f.error,s="."+a,l="module-"+a,c=T(this),u=T(A),m=T(f.scrollContext),g=(c.selector,c.data(l)),p=A.requestAnimationFrame||A.mozRequestAnimationFrame||A.webkitRequestAnimationFrame||A.msRequestAnimationFrame||function(e){setTimeout(e,0)},h=this;d={initialize:function(){d.determineContainer(),d.determineContext(),d.verbose("Initializing sticky",f,i),d.save.positions(),d.checkErrors(),d.bind.events(),f.observeChanges&&d.observeChanges(),d.instantiate()},instantiate:function(){d.verbose("Storing instance of module",d),g=d,c.data(l,d)},destroy:function(){d.verbose("Destroying previous instance"),d.reset(),e&&e.disconnect(),t&&t.disconnect(),u.off("load"+s,d.event.load).off("resize"+s,d.event.resize),m.off("scrollchange"+s,d.event.scrollchange),c.removeData(l)},observeChanges:function(){"MutationObserver"in A&&(e=new MutationObserver(d.event.documentChanged),t=new MutationObserver(d.event.changed),e.observe(R,{childList:!0,subtree:!0}),t.observe(h,{childList:!0,subtree:!0}),t.observe(o[0],{childList:!0,subtree:!0}),d.debug("Setting up mutation observer",t))},determineContainer:function(){i=f.container?T(f.container):c.offsetParent()},determineContext:function(){0!==(o=f.context?T(f.context):i).length||d.error(r.invalidContext,f.context,c)},checkErrors:function(){if(d.is.hidden()&&d.error(r.visible,c),d.cache.element.height>d.cache.context.height)return d.reset(),void d.error(r.elementSize,c)},bind:{events:function(){u.on("load"+s,d.event.load).on("resize"+s,d.event.resize),m.off("scroll"+s).on("scroll"+s,d.event.scroll).on("scrollchange"+s,d.event.scrollchange)}},event:{changed:function(e){clearTimeout(d.timer),d.timer=setTimeout(function(){d.verbose("DOM tree modified, updating sticky menu",e),d.refresh()},100)},documentChanged:function(e){[].forEach.call(e,function(e){e.removedNodes&&[].forEach.call(e.removedNodes,function(e){(e==h||0<T(e).find(h).length)&&(d.debug("Element removed from DOM, tearing down events"),d.destroy())})})},load:function(){d.verbose("Page contents finished loading"),p(d.refresh)},resize:function(){d.verbose("Window resized"),p(d.refresh)},scroll:function(){p(function(){m.triggerHandler("scrollchange"+s,m.scrollTop())})},scrollchange:function(e,t){d.stick(t),f.onScroll.call(h)}},refresh:function(e){d.reset(),f.context||d.determineContext(),e&&d.determineContainer(),d.save.positions(),d.stick(),f.onReposition.call(h)},supports:{sticky:function(){var e=T("<div/>");e[0];return e.addClass(n.supported),e.css("position").match("sticky")}},save:{lastScroll:function(e){d.lastScroll=e},elementScroll:function(e){d.elementScroll=e},positions:function(){var e={height:m.height()},t={margin:{top:parseInt(c.css("margin-top"),10),bottom:parseInt(c.css("margin-bottom"),10)},offset:c.offset(),width:c.outerWidth(),height:c.outerHeight()},n={offset:o.offset(),height:o.outerHeight()};i.outerHeight();d.is.standardScroll()||(d.debug("Non-standard scroll. Removing scroll offset from element offset"),e.top=m.scrollTop(),e.left=m.scrollLeft(),t.offset.top+=e.top,n.offset.top+=e.top,t.offset.left+=e.left,n.offset.left+=e.left),d.cache={fits:t.height+f.offset<=e.height,sameHeight:t.height==n.height,scrollContext:{height:e.height},element:{margin:t.margin,top:t.offset.top-t.margin.top,left:t.offset.left,width:t.width,height:t.height,bottom:t.offset.top+t.height},context:{top:n.offset.top,height:n.height,bottom:n.offset.top+n.height}},d.set.containerSize(),d.stick(),d.debug("Caching element positions",d.cache)}},get:{direction:function(e){var t="down";return e=e||m.scrollTop(),d.lastScroll!==P&&(d.lastScroll<e?t="down":d.lastScroll>e&&(t="up")),t},scrollChange:function(e){return e=e||m.scrollTop(),d.lastScroll?e-d.lastScroll:0},currentElementScroll:function(){return d.elementScroll?d.elementScroll:d.is.top()?Math.abs(parseInt(c.css("top"),10))||0:Math.abs(parseInt(c.css("bottom"),10))||0},elementScroll:function(e){e=e||m.scrollTop();var t=d.cache.element,n=d.cache.scrollContext,i=d.get.scrollChange(e),o=t.height-n.height+f.offset,a=d.get.currentElementScroll(),r=a+i;return a=d.cache.fits||r<0?0:o<r?o:r}},remove:{lastScroll:function(){delete d.lastScroll},elementScroll:function(e){delete d.elementScroll},minimumSize:function(){i.css("min-height","")},offset:function(){c.css("margin-top","")}},set:{offset:function(){d.verbose("Setting offset on element",f.offset),c.css("margin-top",f.offset)},containerSize:function(){var e=i.get(0).tagName;"HTML"===e||"body"==e?d.determineContainer():Math.abs(i.outerHeight()-d.cache.context.height)>f.jitter&&(d.debug("Context has padding, specifying exact height for container",d.cache.context.height),i.css({height:d.cache.context.height}))},minimumSize:function(){var e=d.cache.element;i.css("min-height",e.height)},scroll:function(e){d.debug("Setting scroll on element",e),d.elementScroll!=e&&(d.is.top()&&c.css("bottom","").css("top",-e),d.is.bottom()&&c.css("top","").css("bottom",e))},size:function(){0!==d.cache.element.height&&0!==d.cache.element.width&&(h.style.setProperty("width",d.cache.element.width+"px","important"),h.style.setProperty("height",d.cache.element.height+"px","important"))}},is:{standardScroll:function(){return m[0]==A},top:function(){return c.hasClass(n.top)},bottom:function(){return c.hasClass(n.bottom)},initialPosition:function(){return!d.is.fixed()&&!d.is.bound()},hidden:function(){return!c.is(":visible")},bound:function(){return c.hasClass(n.bound)},fixed:function(){return c.hasClass(n.fixed)}},stick:function(e){var t=e||m.scrollTop(),n=d.cache,i=n.fits,o=n.sameHeight,a=n.element,r=n.scrollContext,s=n.context,l=d.is.bottom()&&f.pushing?f.bottomOffset:f.offset,c=(e={top:t+l,bottom:t+l+r.height},d.get.direction(e.top),i?0:d.get.elementScroll(e.top)),u=!i;0!==a.height&&!o&&(d.is.initialPosition()?e.top>=s.bottom?(d.debug("Initial element position is bottom of container"),d.bindBottom()):e.top>a.top&&(a.height+e.top-c>=s.bottom?(d.debug("Initial element position is bottom of container"),d.bindBottom()):(d.debug("Initial element position is fixed"),d.fixTop())):d.is.fixed()?d.is.top()?e.top<=a.top?(d.debug("Fixed element reached top of container"),d.setInitialPosition()):a.height+e.top-c>=s.bottom?(d.debug("Fixed element reached bottom of container"),d.bindBottom()):u&&(d.set.scroll(c),d.save.lastScroll(e.top),d.save.elementScroll(c)):d.is.bottom()&&(e.bottom-a.height<=a.top?(d.debug("Bottom fixed rail has reached top of container"),d.setInitialPosition()):e.bottom>=s.bottom?(d.debug("Bottom fixed rail has reached bottom of container"),d.bindBottom()):u&&(d.set.scroll(c),d.save.lastScroll(e.top),d.save.elementScroll(c))):d.is.bottom()&&(e.top<=a.top?(d.debug("Jumped from bottom fixed to top fixed, most likely used home/end button"),d.setInitialPosition()):f.pushing?d.is.bound()&&e.bottom<=s.bottom&&(d.debug("Fixing bottom attached element to bottom of browser."),d.fixBottom()):d.is.bound()&&e.top<=s.bottom-a.height&&(d.debug("Fixing bottom attached element to top of browser."),d.fixTop())))},bindTop:function(){d.debug("Binding element to top of parent container"),d.remove.offset(),c.css({left:"",top:"",marginBottom:""}).removeClass(n.fixed).removeClass(n.bottom).addClass(n.bound).addClass(n.top),f.onTop.call(h),f.onUnstick.call(h)},bindBottom:function(){d.debug("Binding element to bottom of parent container"),d.remove.offset(),c.css({left:"",top:""}).removeClass(n.fixed).removeClass(n.top).addClass(n.bound).addClass(n.bottom),f.onBottom.call(h),f.onUnstick.call(h)},setInitialPosition:function(){d.debug("Returning to initial position"),d.unfix(),d.unbind()},fixTop:function(){d.debug("Fixing element to top of page"),f.setSize&&d.set.size(),d.set.minimumSize(),d.set.offset(),c.css({left:d.cache.element.left,bottom:"",marginBottom:""}).removeClass(n.bound).removeClass(n.bottom).addClass(n.fixed).addClass(n.top),f.onStick.call(h)},fixBottom:function(){d.debug("Sticking element to bottom of page"),f.setSize&&d.set.size(),d.set.minimumSize(),d.set.offset(),c.css({left:d.cache.element.left,bottom:"",marginBottom:""}).removeClass(n.bound).removeClass(n.top).addClass(n.fixed).addClass(n.bottom),f.onStick.call(h)},unbind:function(){d.is.bound()&&(d.debug("Removing container bound position on element"),d.remove.offset(),c.removeClass(n.bound).removeClass(n.top).removeClass(n.bottom))},unfix:function(){d.is.fixed()&&(d.debug("Removing fixed position on element"),d.remove.minimumSize(),d.remove.offset(),c.removeClass(n.fixed).removeClass(n.top).removeClass(n.bottom),f.onUnstick.call(h))},reset:function(){d.debug("Resetting elements position"),d.unbind(),d.unfix(),d.resetCSS(),d.remove.offset(),d.remove.lastScroll()},resetCSS:function(){c.css({width:"",height:""}),i.css({height:""})},setting:function(e,t){if(T.isPlainObject(e))T.extend(!0,f,e);else{if(t===P)return f[e];f[e]=t}},internal:function(e,t){if(T.isPlainObject(e))T.extend(!0,d,e);else{if(t===P)return d[e];d[e]=t}},debug:function(){!f.silent&&f.debug&&(f.performance?d.performance.log(arguments):(d.debug=Function.prototype.bind.call(console.info,console,f.name+":"),d.debug.apply(console,arguments)))},verbose:function(){!f.silent&&f.verbose&&f.debug&&(f.performance?d.performance.log(arguments):(d.verbose=Function.prototype.bind.call(console.info,console,f.name+":"),d.verbose.apply(console,arguments)))},error:function(){f.silent||(d.error=Function.prototype.bind.call(console.error,console,f.name+":"),d.error.apply(console,arguments))},performance:{log:function(e){var t,n;f.performance&&(n=(t=(new Date).getTime())-(x||t),x=t,C.push({Name:e[0],Arguments:[].slice.call(e,1)||"",Element:h,"Execution Time":n})),clearTimeout(d.performance.timer),d.performance.timer=setTimeout(d.performance.display,0)},display:function(){var e=f.name+":",n=0;x=!1,clearTimeout(d.performance.timer),T.each(C,function(e,t){n+=t["Execution Time"]}),e+=" "+n+"ms",y&&(e+=" '"+y+"'"),(console.group!==P||console.table!==P)&&0<C.length&&(console.groupCollapsed(e),console.table?console.table(C):T.each(C,function(e,t){console.log(t.Name+": "+t["Execution Time"]+"ms")}),console.groupEnd()),C=[]}},invoke:function(i,e,t){var o,a,n,r=g;return e=e||k,t=h||t,"string"==typeof i&&r!==P&&(i=i.split(/[\. ]/),o=i.length-1,T.each(i,function(e,t){var n=e!=o?t+i[e+1].charAt(0).toUpperCase()+i[e+1].slice(1):i;if(T.isPlainObject(r[n])&&e!=o)r=r[n];else{if(r[n]!==P)return a=r[n],!1;if(!T.isPlainObject(r[t])||e==o)return r[t]!==P&&(a=r[t]),!1;r=r[t]}})),T.isFunction(a)?n=a.apply(t,e):a!==P&&(n=a),T.isArray(b)?b.push(n):b!==P?b=[b,n]:n!==P&&(b=n),a}},S?(g===P&&d.initialize(),d.invoke(w)):(g!==P&&g.invoke("destroy"),d.initialize())}),b!==P?b:this},T.fn.sticky.settings={name:"Sticky",namespace:"sticky",silent:!1,debug:!1,verbose:!0,performance:!0,pushing:!1,context:!1,container:!1,scrollContext:A,offset:0,bottomOffset:0,jitter:5,setSize:!0,observeChanges:!1,onReposition:function(){},onScroll:function(){},onStick:function(){},onUnstick:function(){},onTop:function(){},onBottom:function(){},error:{container:"Sticky element must be inside a relative container",visible:"Element is hidden, you must call refresh after element becomes visible. Use silent setting to surpress this warning in production.",method:"The method you called is not defined.",invalidContext:"Context specified does not exist",elementSize:"Sticky element is larger than its container, cannot create sticky."},className:{bound:"bound",fixed:"fixed",supported:"native",top:"top",bottom:"bottom"}}}(jQuery,window,document),function(E,F,O,D){"use strict";F=void 0!==F&&F.Math==Math?F:"undefined"!=typeof self&&self.Math==Math?self:Function("return this")(),E.fn.tab=function(r){var c,u=E.isFunction(this)?E(F):E(this),d=u.selector||"",f=(new Date).getTime(),m=[],g=r,A="string"==typeof g,R=[].slice.call(arguments,1),P=!1;return u.each(function(){var p,a,h,v,b,y,x=E.isPlainObject(r)?E.extend(!0,{},E.fn.tab.settings,r):E.extend({},E.fn.tab.settings),C=x.className,w=x.metadata,t=x.selector,S=x.error,e="."+x.namespace,n="module-"+x.namespace,k=E(this),i={},T=!0,o=0,s=this,l=k.data(n);b={initialize:function(){b.debug("Initializing tab menu item",k),b.fix.callbacks(),b.determineTabs(),b.debug("Determining tabs",x.context,a),x.auto&&b.set.auto(),b.bind.events(),x.history&&!P&&(b.initializeHistory(),P=!0),b.instantiate()},instantiate:function(){b.verbose("Storing instance of module",b),l=b,k.data(n,b)},destroy:function(){b.debug("Destroying tabs",k),k.removeData(n).off(e)},bind:{events:function(){E.isWindow(s)||(b.debug("Attaching tab activation events to element",k),k.on("click"+e,b.event.click))}},determineTabs:function(){var e;"parent"===x.context?(0<k.closest(t.ui).length?(e=k.closest(t.ui),b.verbose("Using closest UI element as parent",e)):e=k,p=e.parent(),b.verbose("Determined parent element for creating context",p)):x.context?(p=E(x.context),b.verbose("Using selector for tab context",x.context,p)):p=E("body"),x.childrenOnly?(a=p.children(t.tabs),b.debug("Searching tab context children for tabs",p,a)):(a=p.find(t.tabs),b.debug("Searching tab context for tabs",p,a))},fix:{callbacks:function(){E.isPlainObject(r)&&(r.onTabLoad||r.onTabInit)&&(r.onTabLoad&&(r.onLoad=r.onTabLoad,delete r.onTabLoad,b.error(S.legacyLoad,r.onLoad)),r.onTabInit&&(r.onFirstLoad=r.onTabInit,delete r.onTabInit,b.error(S.legacyInit,r.onFirstLoad)),x=E.extend(!0,{},E.fn.tab.settings,r))}},initializeHistory:function(){if(b.debug("Initializing page state"),E.address===D)return b.error(S.state),!1;if("state"==x.historyType){if(b.debug("Using HTML5 to manage state"),!1===x.path)return b.error(S.path),!1;E.address.history(!0).state(x.path)}E.address.bind("change",b.event.history.change)},event:{click:function(e){var t=E(this).data(w.tab);t!==D?(x.history?(b.verbose("Updating page state",e),E.address.value(t)):(b.verbose("Changing tab",e),b.changeTab(t)),e.preventDefault()):b.debug("No tab specified")},history:{change:function(e){var t=e.pathNames.join("/")||b.get.initialPath(),n=x.templates.determineTitle(t)||!1;b.performance.display(),b.debug("History change event",t,e),y=e,t!==D&&b.changeTab(t),n&&E.address.title(n)}}},refresh:function(){h&&(b.debug("Refreshing tab",h),b.changeTab(h))},cache:{read:function(e){return e!==D&&i[e]},add:function(e,t){e=e||h,b.debug("Adding cached content for",e),i[e]=t},remove:function(e){e=e||h,b.debug("Removing cached content for",e),delete i[e]}},set:{auto:function(){var e="string"==typeof x.path?x.path.replace(/\/$/,"")+"/{$tab}":"/{$tab}";b.verbose("Setting up automatic tab retrieval from server",e),E.isPlainObject(x.apiSettings)?x.apiSettings.url=e:x.apiSettings={url:e}},loading:function(e){var t=b.get.tabElement(e);t.hasClass(C.loading)||(b.verbose("Setting loading state for",t),t.addClass(C.loading).siblings(a).removeClass(C.active+" "+C.loading),0<t.length&&x.onRequest.call(t[0],e))},state:function(e){E.address.value(e)}},changeTab:function(d){var f=F.history&&F.history.pushState&&x.ignoreFirstLoad&&T,m=x.auto||E.isPlainObject(x.apiSettings),g=m&&!f?b.utilities.pathToArray(d):b.get.defaultPathArray(d);d=b.utilities.arrayToPath(g),E.each(g,function(e,t){var n,i,o,a,r=g.slice(0,e+1),s=b.utilities.arrayToPath(r),l=b.is.tab(s),c=e+1==g.length,u=b.get.tabElement(s);if(b.verbose("Looking for tab",t),l){if(b.verbose("Tab was found",t),h=s,v=b.utilities.filterArray(g,r),c?a=!0:(i=g.slice(0,e+2),o=b.utilities.arrayToPath(i),(a=!b.is.tab(o))&&b.verbose("Tab parameters found",i)),a&&m)return f?(b.debug("Ignoring remote content on first tab load",s),T=!1,b.cache.add(d,u.html()),b.activate.all(s),x.onFirstLoad.call(u[0],s,v,y),x.onLoad.call(u[0],s,v,y)):(b.activate.navigation(s),b.fetch.content(s,d)),!1;b.debug("Opened local tab",s),b.activate.all(s),b.cache.read(s)||(b.cache.add(s,!0),b.debug("First time tab loaded calling tab init"),x.onFirstLoad.call(u[0],s,v,y)),x.onLoad.call(u[0],s,v,y)}else{if(-1!=d.search("/")||""===d)return b.error(S.missingTab,k,p,s),!1;if(s=(n=E("#"+d+', a[name="'+d+'"]')).closest("[data-tab]").data(w.tab),u=b.get.tabElement(s),n&&0<n.length&&s)return b.debug("Anchor link used, opening parent tab",u,n),u.hasClass(C.active)||setTimeout(function(){b.scrollTo(n)},0),b.activate.all(s),b.cache.read(s)||(b.cache.add(s,!0),b.debug("First time tab loaded calling tab init"),x.onFirstLoad.call(u[0],s,v,y)),x.onLoad.call(u[0],s,v,y),!1}})},scrollTo:function(e){var t=!!(e&&0<e.length)&&e.offset().top;!1!==t&&(b.debug("Forcing scroll to an in-page link in a hidden tab",t,e),E(O).scrollTop(t))},update:{content:function(e,t,n){var i=b.get.tabElement(e),o=i[0];n=n!==D?n:x.evaluateScripts,"string"==typeof x.cacheType&&"dom"==x.cacheType.toLowerCase()&&"string"!=typeof t?i.empty().append(E(t).clone(!0)):n?(b.debug("Updating HTML and evaluating inline scripts",e,t),i.html(t)):(b.debug("Updating HTML",e,t),o.innerHTML=t)}},fetch:{content:function(t,n){var e,i,o=b.get.tabElement(t),a={dataType:"html",encodeParameters:!1,on:"now",cache:x.alwaysRefresh,headers:{"X-Remote":!0},onSuccess:function(e){"response"==x.cacheType&&b.cache.add(n,e),b.update.content(t,e),t==h?(b.debug("Content loaded",t),b.activate.tab(t)):b.debug("Content loaded in background",t),x.onFirstLoad.call(o[0],t,v,y),x.onLoad.call(o[0],t,v,y),x.loadOnce?b.cache.add(n,!0):"string"==typeof x.cacheType&&"dom"==x.cacheType.toLowerCase()&&0<o.children().length?setTimeout(function(){var e=o.children().clone(!0);e=e.not("script"),b.cache.add(n,e)},0):b.cache.add(n,o.html())},urlData:{tab:n}},r=o.api("get request")||!1,s=r&&"pending"===r.state();n=n||t,i=b.cache.read(n),x.cache&&i?(b.activate.tab(t),b.debug("Adding cached content",n),x.loadOnce||("once"==x.evaluateScripts?b.update.content(t,i,!1):b.update.content(t,i)),x.onLoad.call(o[0],t,v,y)):s?(b.set.loading(t),b.debug("Content is already loading",n)):E.api!==D?(e=E.extend(!0,{},x.apiSettings,a),b.debug("Retrieving remote content",n,e),b.set.loading(t),o.api(e)):b.error(S.api)}},activate:{all:function(e){b.activate.tab(e),b.activate.navigation(e)},tab:function(e){var t=b.get.tabElement(e),n="siblings"==x.deactivate?t.siblings(a):a.not(t),i=t.hasClass(C.active);b.verbose("Showing tab content for",t),i||(t.addClass(C.active),n.removeClass(C.active+" "+C.loading),0<t.length&&x.onVisible.call(t[0],e))},navigation:function(e){var t=b.get.navElement(e),n="siblings"==x.deactivate?t.siblings(u):u.not(t),i=t.hasClass(C.active);b.verbose("Activating tab navigation for",t,e),i||(t.addClass(C.active),n.removeClass(C.active+" "+C.loading))}},deactivate:{all:function(){b.deactivate.navigation(),b.deactivate.tabs()},navigation:function(){u.removeClass(C.active)},tabs:function(){a.removeClass(C.active+" "+C.loading)}},is:{tab:function(e){return e!==D&&0<b.get.tabElement(e).length}},get:{initialPath:function(){return u.eq(0).data(w.tab)||a.eq(0).data(w.tab)},path:function(){return E.address.value()},defaultPathArray:function(e){return b.utilities.pathToArray(b.get.defaultPath(e))},defaultPath:function(e){var t=u.filter("[data-"+w.tab+'^="'+e+'/"]').eq(0).data(w.tab)||!1;if(t){if(b.debug("Found default tab",t),o<x.maxDepth)return o++,b.get.defaultPath(t);b.error(S.recursion)}else b.debug("No default tabs found for",e,a);return o=0,e},navElement:function(e){return e=e||h,u.filter("[data-"+w.tab+'="'+e+'"]')},tabElement:function(e){var t,n,i,o;return e=e||h,i=b.utilities.pathToArray(e),o=b.utilities.last(i),t=a.filter("[data-"+w.tab+'="'+e+'"]'),n=a.filter("[data-"+w.tab+'="'+o+'"]'),0<t.length?t:n},tab:function(){return h}},utilities:{filterArray:function(e,t){return E.grep(e,function(e){return-1==E.inArray(e,t)})},last:function(e){return!!E.isArray(e)&&e[e.length-1]},pathToArray:function(e){return e===D&&(e=h),"string"==typeof e?e.split("/"):[e]},arrayToPath:function(e){return!!E.isArray(e)&&e.join("/")}},setting:function(e,t){if(b.debug("Changing setting",e,t),E.isPlainObject(e))E.extend(!0,x,e);else{if(t===D)return x[e];E.isPlainObject(x[e])?E.extend(!0,x[e],t):x[e]=t}},internal:function(e,t){if(E.isPlainObject(e))E.extend(!0,b,e);else{if(t===D)return b[e];b[e]=t}},debug:function(){!x.silent&&x.debug&&(x.performance?b.performance.log(arguments):(b.debug=Function.prototype.bind.call(console.info,console,x.name+":"),b.debug.apply(console,arguments)))},verbose:function(){!x.silent&&x.verbose&&x.debug&&(x.performance?b.performance.log(arguments):(b.verbose=Function.prototype.bind.call(console.info,console,x.name+":"),b.verbose.apply(console,arguments)))},error:function(){x.silent||(b.error=Function.prototype.bind.call(console.error,console,x.name+":"),b.error.apply(console,arguments))},performance:{log:function(e){var t,n;x.performance&&(n=(t=(new Date).getTime())-(f||t),f=t,m.push({Name:e[0],Arguments:[].slice.call(e,1)||"",Element:s,"Execution Time":n})),clearTimeout(b.performance.timer),b.performance.timer=setTimeout(b.performance.display,500)},display:function(){var e=x.name+":",n=0;f=!1,clearTimeout(b.performance.timer),E.each(m,function(e,t){n+=t["Execution Time"]}),e+=" "+n+"ms",d&&(e+=" '"+d+"'"),(console.group!==D||console.table!==D)&&0<m.length&&(console.groupCollapsed(e),console.table?console.table(m):E.each(m,function(e,t){console.log(t.Name+": "+t["Execution Time"]+"ms")}),console.groupEnd()),m=[]}},invoke:function(i,e,t){var o,a,n,r=l;return e=e||R,t=s||t,"string"==typeof i&&r!==D&&(i=i.split(/[\. ]/),o=i.length-1,E.each(i,function(e,t){var n=e!=o?t+i[e+1].charAt(0).toUpperCase()+i[e+1].slice(1):i;if(E.isPlainObject(r[n])&&e!=o)r=r[n];else{if(r[n]!==D)return a=r[n],!1;if(!E.isPlainObject(r[t])||e==o)return r[t]!==D?a=r[t]:b.error(S.method,i),!1;r=r[t]}})),E.isFunction(a)?n=a.apply(t,e):a!==D&&(n=a),E.isArray(c)?c.push(n):c!==D?c=[c,n]:n!==D&&(c=n),a}},A?(l===D&&b.initialize(),b.invoke(g)):(l!==D&&l.invoke("destroy"),b.initialize())}),c!==D?c:this},E.tab=function(){E(F).tab.apply(this,arguments)},E.fn.tab.settings={name:"Tab",namespace:"tab",silent:!1,debug:!1,verbose:!1,performance:!0,auto:!1,history:!1,historyType:"hash",path:!1,context:!1,childrenOnly:!1,maxDepth:25,deactivate:"siblings",alwaysRefresh:!1,cache:!0,loadOnce:!1,cacheType:"response",ignoreFirstLoad:!1,apiSettings:!1,evaluateScripts:"once",onFirstLoad:function(e,t,n){},onLoad:function(e,t,n){},onVisible:function(e,t,n){},onRequest:function(e,t,n){},templates:{determineTitle:function(e){}},error:{api:"You attempted to load content without API module",method:"The method you called is not defined",missingTab:"Activated tab cannot be found. Tabs are case-sensitive.",noContent:"The tab you specified is missing a content url.",path:"History enabled, but no path was specified",recursion:"Max recursive depth reached",legacyInit:"onTabInit has been renamed to onFirstLoad in 2.0, please adjust your code.",legacyLoad:"onTabLoad has been renamed to onLoad in 2.0. Please adjust your code",state:"History requires Asual's Address library <https://github.com/asual/jquery-address>"},metadata:{tab:"tab",loaded:"loaded",promise:"promise"},className:{loading:"loading",active:"active"},selector:{tabs:".ui.tab",ui:".ui"}}}(jQuery,window,document),function(C,e,w,S){"use strict";e=void 0!==e&&e.Math==Math?e:"undefined"!=typeof self&&self.Math==Math?self:Function("return this")(),C.fn.transition=function(){var c,r=C(this),g=r.selector||"",p=(new Date).getTime(),h=[],v=arguments,b=v[0],y=[].slice.call(arguments,1),x="string"==typeof b;e.requestAnimationFrame||e.mozRequestAnimationFrame||e.webkitRequestAnimationFrame||e.msRequestAnimationFrame;return r.each(function(i){var u,s,t,d,n,o,e,a,f,m=C(this),l=this;(f={initialize:function(){u=f.get.settings.apply(l,v),d=u.className,t=u.error,n=u.metadata,a="."+u.namespace,e="module-"+u.namespace,s=m.data(e)||f,o=f.get.animationEndEvent(),x&&(x=f.invoke(b)),!1===x&&(f.verbose("Converted arguments into settings object",u),u.interval?f.delay(u.animate):f.animate(),f.instantiate())},instantiate:function(){f.verbose("Storing instance of module",f),s=f,m.data(e,s)},destroy:function(){f.verbose("Destroying previous module for",l),m.removeData(e)},refresh:function(){f.verbose("Refreshing display type on next animation"),delete f.displayType},forceRepaint:function(){f.verbose("Forcing element repaint");var e=m.parent(),t=m.next();0===t.length?m.detach().appendTo(e):m.detach().insertBefore(t)},repaint:function(){f.verbose("Repainting element");l.offsetWidth},delay:function(e){var t,n=f.get.animationDirection();n||(n=f.can.transition()?f.get.direction():"static"),e=e!==S?e:u.interval,t="auto"==u.reverse&&n==d.outward||1==u.reverse?(r.length-i)*u.interval:i*u.interval,f.debug("Delaying animation by",t),setTimeout(f.animate,t)},animate:function(e){if(u=e||u,!f.is.supported())return f.error(t.support),!1;if(f.debug("Preparing animation",u.animation),f.is.animating()){if(u.queue)return!u.allowRepeats&&f.has.direction()&&f.is.occurring()&&!0!==f.queuing?f.debug("Animation is currently occurring, preventing queueing same animation",u.animation):f.queue(u.animation),!1;if(!u.allowRepeats&&f.is.occurring())return f.debug("Animation is already occurring, will not execute repeated animation",u.animation),!1;f.debug("New animation started, completing previous early",u.animation),s.complete()}f.can.animate()?f.set.animating(u.animation):f.error(t.noAnimation,u.animation,l)},reset:function(){f.debug("Resetting animation to beginning conditions"),f.remove.animationCallbacks(),f.restore.conditions(),f.remove.animating()},queue:function(e){f.debug("Queueing animation of",e),f.queuing=!0,m.one(o+".queue"+a,function(){f.queuing=!1,f.repaint(),f.animate.apply(this,u)})},complete:function(e){f.debug("Animation complete",u.animation),f.remove.completeCallback(),f.remove.failSafe(),f.is.looping()||(f.is.outward()?(f.verbose("Animation is outward, hiding element"),f.restore.conditions(),f.hide()):f.is.inward()?(f.verbose("Animation is outward, showing element"),f.restore.conditions(),f.show()):(f.verbose("Static animation completed"),f.restore.conditions(),u.onComplete.call(l)))},force:{visible:function(){var e=m.attr("style"),t=f.get.userStyle(),n=f.get.displayType(),i=t+"display: "+n+" !important;",o=m.css("display"),a=e===S||""===e;o!==n?(f.verbose("Overriding default display to show element",n),m.attr("style",i)):a&&m.removeAttr("style")},hidden:function(){var e=m.attr("style"),t=m.css("display"),n=e===S||""===e;"none"===t||f.is.hidden()?n&&m.removeAttr("style"):(f.verbose("Overriding default display to hide element"),m.css("display","none"))}},has:{direction:function(e){var n=!1;return"string"==typeof(e=e||u.animation)&&(e=e.split(" "),C.each(e,function(e,t){t!==d.inward&&t!==d.outward||(n=!0)})),n},inlineDisplay:function(){var e=m.attr("style")||"";return C.isArray(e.match(/display.*?;/,""))}},set:{animating:function(e){var t;f.remove.completeCallback(),e=e||u.animation,t=f.get.animationClass(e),f.save.animation(t),f.force.visible(),f.remove.hidden(),f.remove.direction(),f.start.animation(t)},duration:function(e,t){((t="number"==typeof(t=t||u.duration)?t+"ms":t)||0===t)&&(f.verbose("Setting animation duration",t),m.css({"animation-duration":t}))},direction:function(e){(e=e||f.get.direction())==d.inward?f.set.inward():f.set.outward()},looping:function(){f.debug("Transition set to loop"),m.addClass(d.looping)},hidden:function(){m.addClass(d.transition).addClass(d.hidden)},inward:function(){f.debug("Setting direction to inward"),m.removeClass(d.outward).addClass(d.inward)},outward:function(){f.debug("Setting direction to outward"),m.removeClass(d.inward).addClass(d.outward)},visible:function(){m.addClass(d.transition).addClass(d.visible)}},start:{animation:function(e){e=e||f.get.animationClass(),f.debug("Starting tween",e),m.addClass(e).one(o+".complete"+a,f.complete),u.useFailSafe&&f.add.failSafe(),f.set.duration(u.duration),u.onStart.call(l)}},save:{animation:function(e){f.cache||(f.cache={}),f.cache.animation=e},displayType:function(e){"none"!==e&&m.data(n.displayType,e)},transitionExists:function(e,t){C.fn.transition.exists[e]=t,f.verbose("Saving existence of transition",e,t)}},restore:{conditions:function(){var e=f.get.currentAnimation();e&&(m.removeClass(e),f.verbose("Removing animation class",f.cache)),f.remove.duration()}},add:{failSafe:function(){var e=f.get.duration();f.timer=setTimeout(function(){m.triggerHandler(o)},e+u.failSafeDelay),f.verbose("Adding fail safe timer",f.timer)}},remove:{animating:function(){m.removeClass(d.animating)},animationCallbacks:function(){f.remove.queueCallback(),f.remove.completeCallback()},queueCallback:function(){m.off(".queue"+a)},completeCallback:function(){m.off(".complete"+a)},display:function(){m.css("display","")},direction:function(){m.removeClass(d.inward).removeClass(d.outward)},duration:function(){m.css("animation-duration","")},failSafe:function(){f.verbose("Removing fail safe timer",f.timer),f.timer&&clearTimeout(f.timer)},hidden:function(){m.removeClass(d.hidden)},visible:function(){m.removeClass(d.visible)},looping:function(){f.debug("Transitions are no longer looping"),f.is.looping()&&(f.reset(),m.removeClass(d.looping))},transition:function(){m.removeClass(d.visible).removeClass(d.hidden)}},get:{settings:function(e,t,n){return"object"==typeof e?C.extend(!0,{},C.fn.transition.settings,e):"function"==typeof n?C.extend({},C.fn.transition.settings,{animation:e,onComplete:n,duration:t}):"string"==typeof t||"number"==typeof t?C.extend({},C.fn.transition.settings,{animation:e,duration:t}):"object"==typeof t?C.extend({},C.fn.transition.settings,t,{animation:e}):"function"==typeof t?C.extend({},C.fn.transition.settings,{animation:e,onComplete:t}):C.extend({},C.fn.transition.settings,{animation:e})},animationClass:function(e){var t=e||u.animation,n=f.can.transition()&&!f.has.direction()?f.get.direction()+" ":"";return d.animating+" "+d.transition+" "+n+t},currentAnimation:function(){return!(!f.cache||f.cache.animation===S)&&f.cache.animation},currentDirection:function(){return f.is.inward()?d.inward:d.outward},direction:function(){return f.is.hidden()||!f.is.visible()?d.inward:d.outward},animationDirection:function(e){var n;return"string"==typeof(e=e||u.animation)&&(e=e.split(" "),C.each(e,function(e,t){t===d.inward?n=d.inward:t===d.outward&&(n=d.outward)})),n||!1},duration:function(e){return!1===(e=e||u.duration)&&(e=m.css("animation-duration")||0),"string"==typeof e?-1<e.indexOf("ms")?parseFloat(e):1e3*parseFloat(e):e},displayType:function(e){return e=e===S||e,u.displayType?u.displayType:(e&&m.data(n.displayType)===S&&f.can.transition(!0),m.data(n.displayType))},userStyle:function(e){return(e=e||m.attr("style")||"").replace(/display.*?;/,"")},transitionExists:function(e){return C.fn.transition.exists[e]},animationStartEvent:function(){var e,t=w.createElement("div"),n={animation:"animationstart",OAnimation:"oAnimationStart",MozAnimation:"mozAnimationStart",WebkitAnimation:"webkitAnimationStart"};for(e in n)if(t.style[e]!==S)return n[e];return!1},animationEndEvent:function(){var e,t=w.createElement("div"),n={animation:"animationend",OAnimation:"oAnimationEnd",MozAnimation:"mozAnimationEnd",WebkitAnimation:"webkitAnimationEnd"};for(e in n)if(t.style[e]!==S)return n[e];return!1}},can:{transition:function(e){var t,n,i,o,a,r,s=u.animation,l=f.get.transitionExists(s),c=f.get.displayType(!1);if(l===S||e){if(f.verbose("Determining whether animation exists"),t=m.attr("class"),n=m.prop("tagName"),o=(i=C("<"+n+" />").addClass(t).insertAfter(m)).addClass(s).removeClass(d.inward).removeClass(d.outward).addClass(d.animating).addClass(d.transition).css("animationName"),a=i.addClass(d.inward).css("animationName"),c||(c=i.attr("class",t).removeAttr("style").removeClass(d.hidden).removeClass(d.visible).show().css("display"),f.verbose("Determining final display state",c),f.save.displayType(c)),i.remove(),o!=a)f.debug("Direction exists for animation",s),r=!0;else{if("none"==o||!o)return void f.debug("No animation defined in css",s);f.debug("Static animation found",s,c),r=!1}f.save.transitionExists(s,r)}return l!==S?l:r},animate:function(){return f.can.transition()!==S}},is:{animating:function(){return m.hasClass(d.animating)},inward:function(){return m.hasClass(d.inward)},outward:function(){return m.hasClass(d.outward)},looping:function(){return m.hasClass(d.looping)},occurring:function(e){return e="."+(e=e||u.animation).replace(" ","."),0<m.filter(e).length},visible:function(){return m.is(":visible")},hidden:function(){return"hidden"===m.css("visibility")},supported:function(){return!1!==o}},hide:function(){f.verbose("Hiding element"),f.is.animating()&&f.reset(),l.blur(),f.remove.display(),f.remove.visible(),f.set.hidden(),f.force.hidden(),u.onHide.call(l),u.onComplete.call(l)},show:function(e){f.verbose("Showing element",e),f.remove.hidden(),f.set.visible(),f.force.visible(),u.onShow.call(l),u.onComplete.call(l)},toggle:function(){f.is.visible()?f.hide():f.show()},stop:function(){f.debug("Stopping current animation"),m.triggerHandler(o)},stopAll:function(){f.debug("Stopping all animation"),f.remove.queueCallback(),m.triggerHandler(o)},clear:{queue:function(){f.debug("Clearing animation queue"),f.remove.queueCallback()}},enable:function(){f.verbose("Starting animation"),m.removeClass(d.disabled)},disable:function(){f.debug("Stopping animation"),m.addClass(d.disabled)},setting:function(e,t){if(f.debug("Changing setting",e,t),C.isPlainObject(e))C.extend(!0,u,e);else{if(t===S)return u[e];C.isPlainObject(u[e])?C.extend(!0,u[e],t):u[e]=t}},internal:function(e,t){if(C.isPlainObject(e))C.extend(!0,f,e);else{if(t===S)return f[e];f[e]=t}},debug:function(){!u.silent&&u.debug&&(u.performance?f.performance.log(arguments):(f.debug=Function.prototype.bind.call(console.info,console,u.name+":"),f.debug.apply(console,arguments)))},verbose:function(){!u.silent&&u.verbose&&u.debug&&(u.performance?f.performance.log(arguments):(f.verbose=Function.prototype.bind.call(console.info,console,u.name+":"),f.verbose.apply(console,arguments)))},error:function(){u.silent||(f.error=Function.prototype.bind.call(console.error,console,u.name+":"),f.error.apply(console,arguments))},performance:{log:function(e){var t,n;u.performance&&(n=(t=(new Date).getTime())-(p||t),p=t,h.push({Name:e[0],Arguments:[].slice.call(e,1)||"",Element:l,"Execution Time":n})),clearTimeout(f.performance.timer),f.performance.timer=setTimeout(f.performance.display,500)},display:function(){var e=u.name+":",n=0;p=!1,clearTimeout(f.performance.timer),C.each(h,function(e,t){n+=t["Execution Time"]}),e+=" "+n+"ms",g&&(e+=" '"+g+"'"),1<r.length&&(e+=" ("+r.length+")"),(console.group!==S||console.table!==S)&&0<h.length&&(console.groupCollapsed(e),console.table?console.table(h):C.each(h,function(e,t){console.log(t.Name+": "+t["Execution Time"]+"ms")}),console.groupEnd()),h=[]}},invoke:function(i,e,t){var o,a,n,r=s;return e=e||y,t=l||t,"string"==typeof i&&r!==S&&(i=i.split(/[\. ]/),o=i.length-1,C.each(i,function(e,t){var n=e!=o?t+i[e+1].charAt(0).toUpperCase()+i[e+1].slice(1):i;if(C.isPlainObject(r[n])&&e!=o)r=r[n];else{if(r[n]!==S)return a=r[n],!1;if(!C.isPlainObject(r[t])||e==o)return r[t]!==S&&(a=r[t]),!1;r=r[t]}})),C.isFunction(a)?n=a.apply(t,e):a!==S&&(n=a),C.isArray(c)?c.push(n):c!==S?c=[c,n]:n!==S&&(c=n),a!==S&&a}}).initialize()}),c!==S?c:this},C.fn.transition.exists={},C.fn.transition.settings={name:"Transition",silent:!1,debug:!1,verbose:!1,performance:!0,namespace:"transition",interval:0,reverse:"auto",onStart:function(){},onComplete:function(){},onShow:function(){},onHide:function(){},useFailSafe:!0,failSafeDelay:100,allowRepeats:!1,displayType:!1,animation:"fade",duration:!1,queue:!0,metadata:{displayType:"display"},className:{animating:"animating",disabled:"disabled",hidden:"hidden",inward:"in",loading:"loading",looping:"looping",outward:"out",transition:"transition",visible:"visible"},error:{noAnimation:"Element is no longer attached to DOM. Unable to animate.  Use silent setting to surpress this warning in production.",repeated:"That animation is already occurring, cancelling repeated animation",method:"The method you called is not defined",support:"This browser does not support CSS animations"}}}(jQuery,window,document),function(P,E,e,F){"use strict";E=void 0!==E&&E.Math==Math?E:"undefined"!=typeof self&&self.Math==Math?self:Function("return this")();P.api=P.fn.api=function(x){var C,e=P.isFunction(this)?P(E):P(this),w=e.selector||"",S=(new Date).getTime(),k=[],T=x,A="string"==typeof T,R=[].slice.call(arguments,1);return e.each(function(){var a,r,n,e,s,l,c=P.isPlainObject(x)?P.extend(!0,{},P.fn.api.settings,x):P.extend({},P.fn.api.settings),t=c.namespace,i=c.metadata,o=c.selector,u=c.error,d=c.className,f="."+t,m="module-"+t,g=P(this),p=g.closest(o.form),h=c.stateContext?P(c.stateContext):g,v=this,b=h[0],y=g.data(m);l={initialize:function(){A||l.bind.events(),l.instantiate()},instantiate:function(){l.verbose("Storing instance of module",l),y=l,g.data(m,y)},destroy:function(){l.verbose("Destroying previous module for",v),g.removeData(m).off(f)},bind:{events:function(){var e=l.get.event();e?(l.verbose("Attaching API events to element",e),g.on(e+f,l.event.trigger)):"now"==c.on&&(l.debug("Querying API endpoint immediately"),l.query())}},decode:{json:function(e){if(e!==F&&"string"==typeof e)try{e=JSON.parse(e)}catch(e){}return e}},read:{cachedResponse:function(e){var t;if(E.Storage!==F)return t=sessionStorage.getItem(e),l.debug("Using cached response",e,t),t=l.decode.json(t);l.error(u.noStorage)}},write:{cachedResponse:function(e,t){t&&""===t?l.debug("Response empty, not caching",t):E.Storage!==F?(P.isPlainObject(t)&&(t=JSON.stringify(t)),sessionStorage.setItem(e,t),l.verbose("Storing cached response for url",e,t)):l.error(u.noStorage)}},query:function(){if(l.is.disabled())l.debug("Element is disabled API request aborted");else{if(l.is.loading()){if(!c.interruptRequests)return void l.debug("Cancelling request, previous request is still pending");l.debug("Interrupting previous request"),l.abort()}if(c.defaultData&&P.extend(!0,c.urlData,l.get.defaultData()),c.serializeForm&&(c.data=l.add.formData(c.data)),!1===(r=l.get.settings()))return l.cancelled=!0,void l.error(u.beforeSend);if(l.cancelled=!1,(n=l.get.templatedURL())||l.is.mocked()){if((n=l.add.urlData(n))||l.is.mocked()){if(r.url=c.base+n,a=P.extend(!0,{},c,{type:c.method||c.type,data:e,url:c.base+n,beforeSend:c.beforeXHR,success:function(){},failure:function(){},complete:function(){}}),l.debug("Querying URL",a.url),l.verbose("Using AJAX settings",a),"local"===c.cache&&l.read.cachedResponse(n))return l.debug("Response returned from local cache"),l.request=l.create.request(),void l.request.resolveWith(b,[l.read.cachedResponse(n)]);c.throttle?c.throttleFirstRequest||l.timer?(l.debug("Throttling request",c.throttle),clearTimeout(l.timer),l.timer=setTimeout(function(){l.timer&&delete l.timer,l.debug("Sending throttled request",e,a.method),l.send.request()},c.throttle)):(l.debug("Sending request",e,a.method),l.send.request(),l.timer=setTimeout(function(){},c.throttle)):(l.debug("Sending request",e,a.method),l.send.request())}}else l.error(u.missingURL)}},should:{removeError:function(){return!0===c.hideError||"auto"===c.hideError&&!l.is.form()}},is:{disabled:function(){return 0<g.filter(o.disabled).length},expectingJSON:function(){return"json"===c.dataType||"jsonp"===c.dataType},form:function(){return g.is("form")||h.is("form")},mocked:function(){return c.mockResponse||c.mockResponseAsync||c.response||c.responseAsync},input:function(){return g.is("input")},loading:function(){return!!l.request&&"pending"==l.request.state()},abortedRequest:function(e){return e&&e.readyState!==F&&0===e.readyState?(l.verbose("XHR request determined to be aborted"),!0):(l.verbose("XHR request was not aborted"),!1)},validResponse:function(e){return l.is.expectingJSON()&&P.isFunction(c.successTest)?(l.debug("Checking JSON returned success",c.successTest,e),c.successTest(e)?(l.debug("Response passed success test",e),!0):(l.debug("Response failed success test",e),!1)):(l.verbose("Response is not JSON, skipping validation",c.successTest,e),!0)}},was:{cancelled:function(){return l.cancelled||!1},succesful:function(){return l.request&&"resolved"==l.request.state()},failure:function(){return l.request&&"rejected"==l.request.state()},complete:function(){return l.request&&("resolved"==l.request.state()||"rejected"==l.request.state())}},add:{urlData:function(o,a){var e,t;return o&&(e=o.match(c.regExp.required),t=o.match(c.regExp.optional),a=a||c.urlData,e&&(l.debug("Looking for required URL variables",e),P.each(e,function(e,t){var n=-1!==t.indexOf("$")?t.substr(2,t.length-3):t.substr(1,t.length-2),i=P.isPlainObject(a)&&a[n]!==F?a[n]:g.data(n)!==F?g.data(n):h.data(n)!==F?h.data(n):a[n];if(i===F)return l.error(u.requiredParameter,n,o),o=!1;l.verbose("Found required variable",n,i),i=c.encodeParameters?l.get.urlEncodedValue(i):i,o=o.replace(t,i)})),t&&(l.debug("Looking for optional URL variables",e),P.each(t,function(e,t){var n=-1!==t.indexOf("$")?t.substr(3,t.length-4):t.substr(2,t.length-3),i=P.isPlainObject(a)&&a[n]!==F?a[n]:g.data(n)!==F?g.data(n):h.data(n)!==F?h.data(n):a[n];o=i!==F?(l.verbose("Optional variable Found",n,i),o.replace(t,i)):(l.verbose("Optional variable not found",n),-1!==o.indexOf("/"+t)?o.replace("/"+t,""):o.replace(t,""))}))),o},formData:function(e){var t=P.fn.serializeObject!==F,n=t?p.serializeObject():p.serialize();return e=e||c.data,e=P.isPlainObject(e)?t?(l.debug("Extending existing data with form data",e,n),P.extend(!0,{},e,n)):(l.error(u.missingSerialize),l.debug("Cant extend data. Replacing data with form data",e,n),n):(l.debug("Adding form data",n),n)}},send:{request:function(){l.set.loading(),l.request=l.create.request(),l.is.mocked()?l.mockedXHR=l.create.mockedXHR():l.xhr=l.create.xhr(),c.onRequest.call(b,l.request,l.xhr)}},event:{trigger:function(e){l.query(),"submit"!=e.type&&"click"!=e.type||e.preventDefault()},xhr:{always:function(){},done:function(e,t,n){var i=this,o=(new Date).getTime()-s,a=c.loadingDuration-o,r=!!P.isFunction(c.onResponse)&&(l.is.expectingJSON()?c.onResponse.call(i,P.extend(!0,{},e)):c.onResponse.call(i,e));a=0<a?a:0,r&&(l.debug("Modified API response in onResponse callback",c.onResponse,r,e),e=r),0<a&&l.debug("Response completed early delaying state change by",a),setTimeout(function(){l.is.validResponse(e)?l.request.resolveWith(i,[e,n]):l.request.rejectWith(i,[n,"invalid"])},a)},fail:function(e,t,n){var i=this,o=(new Date).getTime()-s,a=c.loadingDuration-o;0<(a=0<a?a:0)&&l.debug("Response completed early delaying state change by",a),setTimeout(function(){l.is.abortedRequest(e)?l.request.rejectWith(i,[e,"aborted",n]):l.request.rejectWith(i,[e,"error",t,n])},a)}},request:{done:function(e,t){l.debug("Successful API Response",e),"local"===c.cache&&n&&(l.write.cachedResponse(n,e),l.debug("Saving server response locally",l.cache)),c.onSuccess.call(b,e,g,t)},complete:function(e,t){var n,i;l.was.succesful()?(i=e,n=t):(n=e,i=l.get.responseFromXHR(n)),l.remove.loading(),c.onComplete.call(b,i,g,n)},fail:function(e,t,n){var i=l.get.responseFromXHR(e),o=l.get.errorFromRequest(i,t,n);if("aborted"==t)return l.debug("XHR Aborted (Most likely caused by page navigation or CORS Policy)",t,n),c.onAbort.call(b,t,g,e),!0;"invalid"==t?l.debug("JSON did not pass success test. A server-side error has most likely occurred",i):"error"==t&&e!==F&&(l.debug("XHR produced a server error",t,n),200!=e.status&&n!==F&&""!==n&&l.error(u.statusMessage+n,a.url),c.onError.call(b,o,g,e)),c.errorDuration&&"aborted"!==t&&(l.debug("Adding error state"),l.set.error(),l.should.removeError()&&setTimeout(l.remove.error,c.errorDuration)),l.debug("API Request failed",o,e),c.onFailure.call(b,i,g,e)}}},create:{request:function(){return P.Deferred().always(l.event.request.complete).done(l.event.request.done).fail(l.event.request.fail)},mockedXHR:function(){var e,t,n,i=c.mockResponse||c.response,o=c.mockResponseAsync||c.responseAsync;return n=P.Deferred().always(l.event.xhr.complete).done(l.event.xhr.done).fail(l.event.xhr.fail),i?(t=P.isFunction(i)?(l.debug("Using specified synchronous callback",i),i.call(b,r)):(l.debug("Using settings specified response",i),i),n.resolveWith(b,[t,!1,{responseText:t}])):P.isFunction(o)&&(e=function(e){l.debug("Async callback returned response",e),e?n.resolveWith(b,[e,!1,{responseText:e}]):n.rejectWith(b,[{responseText:e},!1,!1])},l.debug("Using specified async response callback",o),o.call(b,r,e)),n},xhr:function(){var e;return e=P.ajax(a).always(l.event.xhr.always).done(l.event.xhr.done).fail(l.event.xhr.fail),l.verbose("Created server request",e,a),e}},set:{error:function(){l.verbose("Adding error state to element",h),h.addClass(d.error)},loading:function(){l.verbose("Adding loading state to element",h),h.addClass(d.loading),s=(new Date).getTime()}},remove:{error:function(){l.verbose("Removing error state from element",h),h.removeClass(d.error)},loading:function(){l.verbose("Removing loading state from element",h),h.removeClass(d.loading)}},get:{responseFromXHR:function(e){return!!P.isPlainObject(e)&&(l.is.expectingJSON()?l.decode.json(e.responseText):e.responseText)},errorFromRequest:function(e,t,n){return P.isPlainObject(e)&&e.error!==F?e.error:c.error[t]!==F?c.error[t]:n},request:function(){return l.request||!1},xhr:function(){return l.xhr||!1},settings:function(){var e;return(e=c.beforeSend.call(b,c))&&(e.success!==F&&(l.debug("Legacy success callback detected",e),l.error(u.legacyParameters,e.success),e.onSuccess=e.success),e.failure!==F&&(l.debug("Legacy failure callback detected",e),l.error(u.legacyParameters,e.failure),e.onFailure=e.failure),e.complete!==F&&(l.debug("Legacy complete callback detected",e),l.error(u.legacyParameters,e.complete),e.onComplete=e.complete)),e===F&&l.error(u.noReturnedValue),!1===e?e:e!==F?P.extend(!0,{},e):P.extend(!0,{},c)},urlEncodedValue:function(e){var t=E.decodeURIComponent(e),n=E.encodeURIComponent(e);return t!==e?(l.debug("URL value is already encoded, avoiding double encoding",e),e):(l.verbose("Encoding value using encodeURIComponent",e,n),n)},defaultData:function(){var e={};return P.isWindow(v)||(l.is.input()?e.value=g.val():l.is.form()||(e.text=g.text())),e},event:function(){return P.isWindow(v)||"now"==c.on?(l.debug("API called without element, no events attached"),!1):"auto"==c.on?g.is("input")?v.oninput!==F?"input":v.onpropertychange!==F?"propertychange":"keyup":g.is("form")?"submit":"click":c.on},templatedURL:function(e){if(e=e||g.data(i.action)||c.action||!1,n=g.data(i.url)||c.url||!1)return l.debug("Using specified url",n),n;if(e){if(l.debug("Looking up url for action",e,c.api),c.api[e]===F&&!l.is.mocked())return void l.error(u.missingAction,c.action,c.api);n=c.api[e]}else l.is.form()&&(n=g.attr("action")||h.attr("action")||!1,l.debug("No url or action specified, defaulting to form action",n));return n}},abort:function(){var e=l.get.xhr();e&&"resolved"!==e.state()&&(l.debug("Cancelling API request"),e.abort())},reset:function(){l.remove.error(),l.remove.loading()},setting:function(e,t){if(l.debug("Changing setting",e,t),P.isPlainObject(e))P.extend(!0,c,e);else{if(t===F)return c[e];P.isPlainObject(c[e])?P.extend(!0,c[e],t):c[e]=t}},internal:function(e,t){if(P.isPlainObject(e))P.extend(!0,l,e);else{if(t===F)return l[e];l[e]=t}},debug:function(){!c.silent&&c.debug&&(c.performance?l.performance.log(arguments):(l.debug=Function.prototype.bind.call(console.info,console,c.name+":"),l.debug.apply(console,arguments)))},verbose:function(){!c.silent&&c.verbose&&c.debug&&(c.performance?l.performance.log(arguments):(l.verbose=Function.prototype.bind.call(console.info,console,c.name+":"),l.verbose.apply(console,arguments)))},error:function(){c.silent||(l.error=Function.prototype.bind.call(console.error,console,c.name+":"),l.error.apply(console,arguments))},performance:{log:function(e){var t,n;c.performance&&(n=(t=(new Date).getTime())-(S||t),S=t,k.push({Name:e[0],Arguments:[].slice.call(e,1)||"","Execution Time":n})),clearTimeout(l.performance.timer),l.performance.timer=setTimeout(l.performance.display,500)},display:function(){var e=c.name+":",n=0;S=!1,clearTimeout(l.performance.timer),P.each(k,function(e,t){n+=t["Execution Time"]}),e+=" "+n+"ms",w&&(e+=" '"+w+"'"),(console.group!==F||console.table!==F)&&0<k.length&&(console.groupCollapsed(e),console.table?console.table(k):P.each(k,function(e,t){console.log(t.Name+": "+t["Execution Time"]+"ms")}),console.groupEnd()),k=[]}},invoke:function(i,e,t){var o,a,n,r=y;return e=e||R,t=v||t,"string"==typeof i&&r!==F&&(i=i.split(/[\. ]/),o=i.length-1,P.each(i,function(e,t){var n=e!=o?t+i[e+1].charAt(0).toUpperCase()+i[e+1].slice(1):i;if(P.isPlainObject(r[n])&&e!=o)r=r[n];else{if(r[n]!==F)return a=r[n],!1;if(!P.isPlainObject(r[t])||e==o)return r[t]!==F?a=r[t]:l.error(u.method,i),!1;r=r[t]}})),P.isFunction(a)?n=a.apply(t,e):a!==F&&(n=a),P.isArray(C)?C.push(n):C!==F?C=[C,n]:n!==F&&(C=n),a}},A?(y===F&&l.initialize(),l.invoke(T)):(y!==F&&y.invoke("destroy"),l.initialize())}),C!==F?C:this},P.api.settings={name:"API",namespace:"api",debug:!1,verbose:!1,performance:!0,api:{},cache:!0,interruptRequests:!0,on:"auto",stateContext:!1,loadingDuration:0,hideError:"auto",errorDuration:2e3,encodeParameters:!0,action:!1,url:!1,base:"",urlData:{},defaultData:!0,serializeForm:!1,throttle:0,throttleFirstRequest:!0,method:"get",data:{},dataType:"json",mockResponse:!1,mockResponseAsync:!1,response:!1,responseAsync:!1,beforeSend:function(e){return e},beforeXHR:function(e){},onRequest:function(e,t){},onResponse:!1,onSuccess:function(e,t){},onComplete:function(e,t){},onFailure:function(e,t){},onError:function(e,t){},onAbort:function(e,t){},successTest:!1,error:{beforeSend:"The before send function has aborted the request",error:"There was an error with your request",exitConditions:"API Request Aborted. Exit conditions met",JSONParse:"JSON could not be parsed during error handling",legacyParameters:"You are using legacy API success callback names",method:"The method you called is not defined",missingAction:"API action used but no url was defined",missingSerialize:"jquery-serialize-object is required to add form data to an existing data object",missingURL:"No URL specified for api event",noReturnedValue:"The beforeSend callback must return a settings object, beforeSend ignored.",noStorage:"Caching responses locally requires session storage",parseError:"There was an error parsing your request",requiredParameter:"Missing a required URL parameter: ",statusMessage:"Server gave an error: ",timeout:"Your request timed out"},regExp:{required:/\{\$*[A-z0-9]+\}/g,optional:/\{\/\$*[A-z0-9]+\}/g},className:{loading:"loading",error:"error"},selector:{disabled:".disabled",form:"form"},metadata:{action:"action",url:"url"}}}(jQuery,window,document),function(P,E,F,O){"use strict";E=void 0!==E&&E.Math==Math?E:"undefined"!=typeof self&&self.Math==Math?self:Function("return this")(),P.fn.visibility=function(b){var y,e=P(this),x=e.selector||"",C=(new Date).getTime(),w=[],S=b,k="string"==typeof S,T=[].slice.call(arguments,1),A=e.length,R=0;return e.each(function(){var e,t,n,s,o=P.isPlainObject(b)?P.extend(!0,{},P.fn.visibility.settings,b):P.extend({},P.fn.visibility.settings),i=o.className,a=o.namespace,l=o.error,r=o.metadata,c="."+a,u="module-"+a,d=P(E),f=P(this),m=P(o.context),g=(f.selector,f.data(u)),p=E.requestAnimationFrame||E.mozRequestAnimationFrame||E.webkitRequestAnimationFrame||E.msRequestAnimationFrame||function(e){setTimeout(e,0)},h=this,v=!1;s={initialize:function(){s.debug("Initializing",o),s.setup.cache(),s.should.trackChanges()&&("image"==o.type&&s.setup.image(),"fixed"==o.type&&s.setup.fixed(),o.observeChanges&&s.observeChanges(),s.bind.events()),s.save.position(),s.is.visible()||s.error(l.visible,f),o.initialCheck&&s.checkVisibility(),s.instantiate()},instantiate:function(){s.debug("Storing instance",s),f.data(u,s),g=s},destroy:function(){s.verbose("Destroying previous module"),n&&n.disconnect(),t&&t.disconnect(),d.off("load"+c,s.event.load).off("resize"+c,s.event.resize),m.off("scroll"+c,s.event.scroll).off("scrollchange"+c,s.event.scrollchange),"fixed"==o.type&&(s.resetFixed(),s.remove.placeholder()),f.off(c).removeData(u)},observeChanges:function(){"MutationObserver"in E&&(t=new MutationObserver(s.event.contextChanged),n=new MutationObserver(s.event.changed),t.observe(F,{childList:!0,subtree:!0}),n.observe(h,{childList:!0,subtree:!0}),s.debug("Setting up mutation observer",n))},bind:{events:function(){s.verbose("Binding visibility events to scroll and resize"),o.refreshOnLoad&&d.on("load"+c,s.event.load),d.on("resize"+c,s.event.resize),m.off("scroll"+c).on("scroll"+c,s.event.scroll).on("scrollchange"+c,s.event.scrollchange)}},event:{changed:function(e){s.verbose("DOM tree modified, updating visibility calculations"),s.timer=setTimeout(function(){s.verbose("DOM tree modified, updating sticky menu"),s.refresh()},100)},contextChanged:function(e){[].forEach.call(e,function(e){e.removedNodes&&[].forEach.call(e.removedNodes,function(e){(e==h||0<P(e).find(h).length)&&(s.debug("Element removed from DOM, tearing down events"),s.destroy())})})},resize:function(){s.debug("Window resized"),o.refreshOnResize&&p(s.refresh)},load:function(){s.debug("Page finished loading"),p(s.refresh)},scroll:function(){o.throttle?(clearTimeout(s.timer),s.timer=setTimeout(function(){m.triggerHandler("scrollchange"+c,[m.scrollTop()])},o.throttle)):p(function(){m.triggerHandler("scrollchange"+c,[m.scrollTop()])})},scrollchange:function(e,t){s.checkVisibility(t)}},precache:function(e,t){e instanceof Array||(e=[e]);for(var n=e.length,i=0,o=[],a=F.createElement("img"),r=function(){++i>=e.length&&P.isFunction(t)&&t()};n--;)(a=F.createElement("img")).onload=r,a.onerror=r,a.src=e[n],o.push(a)},enableCallbacks:function(){s.debug("Allowing callbacks to occur"),v=!1},disableCallbacks:function(){s.debug("Disabling all callbacks temporarily"),v=!0},should:{trackChanges:function(){return k?(s.debug("One time query, no need to bind events"),!1):(s.debug("Callbacks being attached"),!0)}},setup:{cache:function(){s.cache={occurred:{},screen:{},element:{}}},image:function(){var e=f.data(r.src);e&&(s.verbose("Lazy loading image",e),o.once=!0,o.observeChanges=!1,o.onOnScreen=function(){s.debug("Image on screen",h),s.precache(e,function(){s.set.image(e,function(){++R==A&&o.onAllLoaded.call(this),o.onLoad.call(this)})})})},fixed:function(){s.debug("Setting up fixed"),o.once=!1,o.observeChanges=!1,o.initialCheck=!0,o.refreshOnLoad=!0,b.transition||(o.transition=!1),s.create.placeholder(),s.debug("Added placeholder",e),o.onTopPassed=function(){s.debug("Element passed, adding fixed position",f),s.show.placeholder(),s.set.fixed(),o.transition&&P.fn.transition!==O&&f.transition(o.transition,o.duration)},o.onTopPassedReverse=function(){s.debug("Element returned to position, removing fixed",f),s.hide.placeholder(),s.remove.fixed()}}},create:{placeholder:function(){s.verbose("Creating fixed position placeholder"),e=f.clone(!1).css("display","none").addClass(i.placeholder).insertAfter(f)}},show:{placeholder:function(){s.verbose("Showing placeholder"),e.css("display","block").css("visibility","hidden")}},hide:{placeholder:function(){s.verbose("Hiding placeholder"),e.css("display","none").css("visibility","")}},set:{fixed:function(){s.verbose("Setting element to fixed position"),f.addClass(i.fixed).css({position:"fixed",top:o.offset+"px",left:"auto",zIndex:o.zIndex}),o.onFixed.call(h)},image:function(e,t){if(f.attr("src",e),o.transition)if(P.fn.transition!==O){if(f.hasClass(i.visible))return void s.debug("Transition already occurred on this image, skipping animation");f.transition(o.transition,o.duration,t)}else f.fadeIn(o.duration,t);else f.show()}},is:{onScreen:function(){return s.get.elementCalculations().onScreen},offScreen:function(){return s.get.elementCalculations().offScreen},visible:function(){return!(!s.cache||!s.cache.element)&&!(0===s.cache.element.width&&0===s.cache.element.offset.top)},verticallyScrollableContext:function(){var e=m.get(0)!==E&&m.css("overflow-y");return"auto"==e||"scroll"==e},horizontallyScrollableContext:function(){var e=m.get(0)!==E&&m.css("overflow-x");return"auto"==e||"scroll"==e}},refresh:function(){s.debug("Refreshing constants (width/height)"),"fixed"==o.type&&s.resetFixed(),s.reset(),s.save.position(),o.checkOnRefresh&&s.checkVisibility(),o.onRefresh.call(h)},resetFixed:function(){s.remove.fixed(),s.remove.occurred()},reset:function(){s.verbose("Resetting all cached values"),P.isPlainObject(s.cache)&&(s.cache.screen={},s.cache.element={})},checkVisibility:function(e){s.verbose("Checking visibility of element",s.cache.element),!v&&s.is.visible()&&(s.save.scroll(e),s.save.calculations(),s.passed(),s.passingReverse(),s.topVisibleReverse(),s.bottomVisibleReverse(),s.topPassedReverse(),s.bottomPassedReverse(),s.onScreen(),s.offScreen(),s.passing(),s.topVisible(),s.bottomVisible(),s.topPassed(),s.bottomPassed(),o.onUpdate&&o.onUpdate.call(h,s.get.elementCalculations()))},passed:function(e,t){var n=s.get.elementCalculations();if(e&&t)o.onPassed[e]=t;else{if(e!==O)return s.get.pixelsPassed(e)>n.pixelsPassed;n.passing&&P.each(o.onPassed,function(e,t){n.bottomVisible||n.pixelsPassed>s.get.pixelsPassed(e)?s.execute(t,e):o.once||s.remove.occurred(t)})}},onScreen:function(e){var t=s.get.elementCalculations(),n=e||o.onOnScreen,i="onScreen";if(e&&(s.debug("Adding callback for onScreen",e),o.onOnScreen=e),t.onScreen?s.execute(n,i):o.once||s.remove.occurred(i),e!==O)return t.onOnScreen},offScreen:function(e){var t=s.get.elementCalculations(),n=e||o.onOffScreen,i="offScreen";if(e&&(s.debug("Adding callback for offScreen",e),o.onOffScreen=e),t.offScreen?s.execute(n,i):o.once||s.remove.occurred(i),e!==O)return t.onOffScreen},passing:function(e){var t=s.get.elementCalculations(),n=e||o.onPassing,i="passing";if(e&&(s.debug("Adding callback for passing",e),o.onPassing=e),t.passing?s.execute(n,i):o.once||s.remove.occurred(i),e!==O)return t.passing},topVisible:function(e){var t=s.get.elementCalculations(),n=e||o.onTopVisible,i="topVisible";if(e&&(s.debug("Adding callback for top visible",e),o.onTopVisible=e),t.topVisible?s.execute(n,i):o.once||s.remove.occurred(i),e===O)return t.topVisible},bottomVisible:function(e){var t=s.get.elementCalculations(),n=e||o.onBottomVisible,i="bottomVisible";if(e&&(s.debug("Adding callback for bottom visible",e),o.onBottomVisible=e),t.bottomVisible?s.execute(n,i):o.once||s.remove.occurred(i),e===O)return t.bottomVisible},topPassed:function(e){var t=s.get.elementCalculations(),n=e||o.onTopPassed,i="topPassed";if(e&&(s.debug("Adding callback for top passed",e),o.onTopPassed=e),t.topPassed?s.execute(n,i):o.once||s.remove.occurred(i),e===O)return t.topPassed},bottomPassed:function(e){var t=s.get.elementCalculations(),n=e||o.onBottomPassed,i="bottomPassed";if(e&&(s.debug("Adding callback for bottom passed",e),o.onBottomPassed=e),t.bottomPassed?s.execute(n,i):o.once||s.remove.occurred(i),e===O)return t.bottomPassed},passingReverse:function(e){var t=s.get.elementCalculations(),n=e||o.onPassingReverse,i="passingReverse";if(e&&(s.debug("Adding callback for passing reverse",e),o.onPassingReverse=e),t.passing?o.once||s.remove.occurred(i):s.get.occurred("passing")&&s.execute(n,i),e!==O)return!t.passing},topVisibleReverse:function(e){var t=s.get.elementCalculations(),n=e||o.onTopVisibleReverse,i="topVisibleReverse";if(e&&(s.debug("Adding callback for top visible reverse",e),o.onTopVisibleReverse=e),t.topVisible?o.once||s.remove.occurred(i):s.get.occurred("topVisible")&&s.execute(n,i),e===O)return!t.topVisible},bottomVisibleReverse:function(e){var t=s.get.elementCalculations(),n=e||o.onBottomVisibleReverse,i="bottomVisibleReverse";if(e&&(s.debug("Adding callback for bottom visible reverse",e),o.onBottomVisibleReverse=e),t.bottomVisible?o.once||s.remove.occurred(i):s.get.occurred("bottomVisible")&&s.execute(n,i),e===O)return!t.bottomVisible},topPassedReverse:function(e){var t=s.get.elementCalculations(),n=e||o.onTopPassedReverse,i="topPassedReverse";if(e&&(s.debug("Adding callback for top passed reverse",e),o.onTopPassedReverse=e),t.topPassed?o.once||s.remove.occurred(i):s.get.occurred("topPassed")&&s.execute(n,i),e===O)return!t.onTopPassed},bottomPassedReverse:function(e){var t=s.get.elementCalculations(),n=e||o.onBottomPassedReverse,i="bottomPassedReverse";if(e&&(s.debug("Adding callback for bottom passed reverse",e),o.onBottomPassedReverse=e),t.bottomPassed?o.once||s.remove.occurred(i):s.get.occurred("bottomPassed")&&s.execute(n,i),e===O)return!t.bottomPassed},execute:function(e,t){var n=s.get.elementCalculations(),i=s.get.screenCalculations();(e=e||!1)&&(o.continuous?(s.debug("Callback being called continuously",t,n),e.call(h,n,i)):s.get.occurred(t)||(s.debug("Conditions met",t,n),e.call(h,n,i))),s.save.occurred(t)},remove:{fixed:function(){s.debug("Removing fixed position"),f.removeClass(i.fixed).css({position:"",top:"",left:"",zIndex:""}),o.onUnfixed.call(h)},placeholder:function(){s.debug("Removing placeholder content"),e&&e.remove()},occurred:function(e){if(e){var t=s.cache.occurred;t[e]!==O&&!0===t[e]&&(s.debug("Callback can now be called again",e),s.cache.occurred[e]=!1)}else s.cache.occurred={}}},save:{calculations:function(){s.verbose("Saving all calculations necessary to determine positioning"),s.save.direction(),s.save.screenCalculations(),s.save.elementCalculations()},occurred:function(e){e&&(s.cache.occurred[e]!==O&&!0===s.cache.occurred[e]||(s.verbose("Saving callback occurred",e),s.cache.occurred[e]=!0))},scroll:function(e){e=e+o.offset||m.scrollTop()+o.offset,s.cache.scroll=e},direction:function(){var e,t=s.get.scroll(),n=s.get.lastScroll();return e=n<t&&n?"down":t<n&&n?"up":"static",s.cache.direction=e,s.cache.direction},elementPosition:function(){var e=s.cache.element,t=s.get.screenSize();return s.verbose("Saving element position"),e.fits=e.height<t.height,e.offset=f.offset(),e.width=f.outerWidth(),e.height=f.outerHeight(),s.is.verticallyScrollableContext()&&(e.offset.top+=m.scrollTop()-m.offset().top),s.is.horizontallyScrollableContext()&&(e.offset.left+=m.scrollLeft-m.offset().left),s.cache.element=e},elementCalculations:function(){var e=s.get.screenCalculations(),t=s.get.elementPosition();return o.includeMargin?(t.margin={},t.margin.top=parseInt(f.css("margin-top"),10),t.margin.bottom=parseInt(f.css("margin-bottom"),10),t.top=t.offset.top-t.margin.top,t.bottom=t.offset.top+t.height+t.margin.bottom):(t.top=t.offset.top,t.bottom=t.offset.top+t.height),t.topPassed=e.top>=t.top,t.bottomPassed=e.top>=t.bottom,t.topVisible=e.bottom>=t.top&&!t.topPassed,t.bottomVisible=e.bottom>=t.bottom&&!t.bottomPassed,t.pixelsPassed=0,t.percentagePassed=0,t.onScreen=(t.topVisible||t.passing)&&!t.bottomPassed,t.passing=t.topPassed&&!t.bottomPassed,t.offScreen=!t.onScreen,t.passing&&(t.pixelsPassed=e.top-t.top,t.percentagePassed=(e.top-t.top)/t.height),s.cache.element=t,s.verbose("Updated element calculations",t),t},screenCalculations:function(){var e=s.get.scroll();return s.save.direction(),s.cache.screen.top=e,s.cache.screen.bottom=e+s.cache.screen.height,s.cache.screen},screenSize:function(){s.verbose("Saving window position"),s.cache.screen={height:m.height()}},position:function(){s.save.screenSize(),s.save.elementPosition()}},get:{pixelsPassed:function(e){var t=s.get.elementCalculations();return-1<e.search("%")?t.height*(parseInt(e,10)/100):parseInt(e,10)},occurred:function(e){return s.cache.occurred!==O&&s.cache.occurred[e]||!1},direction:function(){return s.cache.direction===O&&s.save.direction(),s.cache.direction},elementPosition:function(){return s.cache.element===O&&s.save.elementPosition(),s.cache.element},elementCalculations:function(){return s.cache.element===O&&s.save.elementCalculations(),s.cache.element},screenCalculations:function(){return s.cache.screen===O&&s.save.screenCalculations(),s.cache.screen},screenSize:function(){return s.cache.screen===O&&s.save.screenSize(),s.cache.screen},scroll:function(){return s.cache.scroll===O&&s.save.scroll(),s.cache.scroll},lastScroll:function(){return s.cache.screen===O?(s.debug("First scroll event, no last scroll could be found"),!1):s.cache.screen.top}},setting:function(e,t){if(P.isPlainObject(e))P.extend(!0,o,e);else{if(t===O)return o[e];o[e]=t}},internal:function(e,t){if(P.isPlainObject(e))P.extend(!0,s,e);else{if(t===O)return s[e];s[e]=t}},debug:function(){!o.silent&&o.debug&&(o.performance?s.performance.log(arguments):(s.debug=Function.prototype.bind.call(console.info,console,o.name+":"),s.debug.apply(console,arguments)))},verbose:function(){!o.silent&&o.verbose&&o.debug&&(o.performance?s.performance.log(arguments):(s.verbose=Function.prototype.bind.call(console.info,console,o.name+":"),s.verbose.apply(console,arguments)))},error:function(){o.silent||(s.error=Function.prototype.bind.call(console.error,console,o.name+":"),s.error.apply(console,arguments))},performance:{log:function(e){var t,n;o.performance&&(n=(t=(new Date).getTime())-(C||t),C=t,w.push({Name:e[0],Arguments:[].slice.call(e,1)||"",Element:h,"Execution Time":n})),clearTimeout(s.performance.timer),s.performance.timer=setTimeout(s.performance.display,500)},display:function(){var e=o.name+":",n=0;C=!1,clearTimeout(s.performance.timer),P.each(w,function(e,t){n+=t["Execution Time"]}),e+=" "+n+"ms",x&&(e+=" '"+x+"'"),(console.group!==O||console.table!==O)&&0<w.length&&(console.groupCollapsed(e),console.table?console.table(w):P.each(w,function(e,t){console.log(t.Name+": "+t["Execution Time"]+"ms")}),console.groupEnd()),w=[]}},invoke:function(i,e,t){var o,a,n,r=g;return e=e||T,t=h||t,"string"==typeof i&&r!==O&&(i=i.split(/[\. ]/),o=i.length-1,P.each(i,function(e,t){var n=e!=o?t+i[e+1].charAt(0).toUpperCase()+i[e+1].slice(1):i;if(P.isPlainObject(r[n])&&e!=o)r=r[n];else{if(r[n]!==O)return a=r[n],!1;if(!P.isPlainObject(r[t])||e==o)return r[t]!==O?a=r[t]:s.error(l.method,i),!1;r=r[t]}})),P.isFunction(a)?n=a.apply(t,e):a!==O&&(n=a),P.isArray(y)?y.push(n):y!==O?y=[y,n]:n!==O&&(y=n),a}},k?(g===O&&s.initialize(),g.save.scroll(),g.save.calculations(),s.invoke(S)):(g!==O&&g.invoke("destroy"),s.initialize())}),y!==O?y:this},P.fn.visibility.settings={name:"Visibility",namespace:"visibility",debug:!1,verbose:!1,performance:!0,observeChanges:!0,initialCheck:!0,refreshOnLoad:!0,refreshOnResize:!0,checkOnRefresh:!0,once:!0,continuous:!1,offset:0,includeMargin:!1,context:E,throttle:!1,type:!1,zIndex:"10",transition:"fade in",duration:1e3,onPassed:{},onOnScreen:!1,onOffScreen:!1,onPassing:!1,onTopVisible:!1,onBottomVisible:!1,onTopPassed:!1,onBottomPassed:!1,onPassingReverse:!1,onTopVisibleReverse:!1,onBottomVisibleReverse:!1,onTopPassedReverse:!1,onBottomPassedReverse:!1,onLoad:function(){},onAllLoaded:function(){},onFixed:function(){},onUnfixed:function(){},onUpdate:!1,onRefresh:function(){},metadata:{src:"src"},className:{fixed:"fixed",placeholder:"placeholder",visible:"visible"},error:{method:"The method you called is not defined.",visible:"Element is hidden, you must call refresh after element becomes visible"}}}(jQuery,window,document);
/* Copyright (C) 1991-2017 Free Software Foundation, Inc.
   This file is part of the GNU C Library.

   The GNU C Library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2.1 of the License, or (at your option) any later version.

   The GNU C Library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public
   License along with the GNU C Library; if not, see
   <http://www.gnu.org/licenses/>.  */
/* This header is separate from features.h so that the compiler can
   include it implicitly at the start of every compilation.  It must
   not itself include <features.h> or any other header that includes
   <features.h> because the implicit include comes before any feature
   test macros that may be defined in a source file before it first
   explicitly includes a system header.  GCC knows the name of this
   header in order to preinclude it.  */
/* glibc's intent is to support the IEC 559 math functionality, real
   and complex.  If the GCC (4.9 and later) predefined macros
   specifying compiler intent are available, use them to determine
   whether the overall intent is to support these features; otherwise,
   presume an older compiler has intent to support these features and
   define these macros by default.  */
/* wchar_t uses Unicode 8.0.0.  Version 8.0 of the Unicode Standard is
   synchronized with ISO/IEC 10646:2014, plus Amendment 1 (published
   2015-05-15).  */
/* We do not support C11 <threads.h>.  */
// Copyright 2011 The Closure Library Authors. All Rights Reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS-IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
/**
 * @fileoverview Abstract cryptographic hash interface.
 *
 * See goog.crypt.Sha1 and goog.crypt.Md5 for sample implementations.
 *
 */
goog.provide('goog.crypt.Hash');
/**
 * Create a cryptographic hash instance.
 *
 * @constructor
 * @struct
 */
goog.crypt.Hash = function() {
  /**
   * The block size for the hasher.
   * @type {number}
   */
  this.blockSize = -1;
};
/**
 * Resets the internal accumulator.
 */
goog.crypt.Hash.prototype.reset = goog.abstractMethod;
/**
 * Adds a byte array (array with values in [0-255] range) or a string (might
 * only contain 8-bit, i.e., Latin1 characters) to the internal accumulator.
 *
 * Many hash functions operate on blocks of data and implement optimizations
 * when a full chunk of data is readily available. Hence it is often preferable
 * to provide large chunks of data (a kilobyte or more) than to repeatedly
 * call the update method with few tens of bytes. If this is not possible, or
 * not feasible, it might be good to provide data in multiplies of hash block
 * size (often 64 bytes). Please see the implementation and performance tests
 * of your favourite hash.
 *
 * @param {Array<number>|Uint8Array|string} bytes Data used for the update.
 * @param {number=} opt_length Number of bytes to use.
 */
goog.crypt.Hash.prototype.update = goog.abstractMethod;
/**
 * @return {!Array<number>} The finalized hash computed
 *     from the internal accumulator.
 */
goog.crypt.Hash.prototype.digest = goog.abstractMethod;
/* Copyright (C) 1991-2017 Free Software Foundation, Inc.
   This file is part of the GNU C Library.

   The GNU C Library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2.1 of the License, or (at your option) any later version.

   The GNU C Library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public
   License along with the GNU C Library; if not, see
   <http://www.gnu.org/licenses/>.  */
/* This header is separate from features.h so that the compiler can
   include it implicitly at the start of every compilation.  It must
   not itself include <features.h> or any other header that includes
   <features.h> because the implicit include comes before any feature
   test macros that may be defined in a source file before it first
   explicitly includes a system header.  GCC knows the name of this
   header in order to preinclude it.  */
/* glibc's intent is to support the IEC 559 math functionality, real
   and complex.  If the GCC (4.9 and later) predefined macros
   specifying compiler intent are available, use them to determine
   whether the overall intent is to support these features; otherwise,
   presume an older compiler has intent to support these features and
   define these macros by default.  */
/* wchar_t uses Unicode 8.0.0.  Version 8.0 of the Unicode Standard is
   synchronized with ISO/IEC 10646:2014, plus Amendment 1 (published
   2015-05-15).  */
/* We do not support C11 <threads.h>.  */
// Copyright 2011 The Closure Library Authors. All Rights Reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS-IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
/**
 * @fileoverview MD5 cryptographic hash.
 * Implementation of http://tools.ietf.org/html/rfc1321 with common
 * optimizations and tweaks (see http://en.wikipedia.org/wiki/MD5).
 *
 * Usage:
 *   var md5 = new goog.crypt.Md5();
 *   md5.update(bytes);
 *   var hash = md5.digest();
 *
 * Performance:
 *   Chrome 23              ~680 Mbit/s
 *   Chrome 13 (in a VM)    ~250 Mbit/s
 *   Firefox 6.0 (in a VM)  ~100 Mbit/s
 *   IE9 (in a VM)           ~27 Mbit/s
 *   Firefox 3.6             ~15 Mbit/s
 *   IE8 (in a VM)           ~13 Mbit/s
 *
 */
goog.provide('goog.crypt.Md5');
goog.require('goog.crypt.Hash');
/**
 * MD5 cryptographic hash constructor.
 * @constructor
 * @extends {goog.crypt.Hash}
 * @final
 * @struct
 */
goog.crypt.Md5 = function() {
  goog.crypt.Md5.base(this, 'constructor');
  this.blockSize = 512 / 8;
  /**
   * Holds the current values of accumulated A-D variables (MD buffer).
   * @type {!Array<number>}
   * @private
   */
  this.chain_ = new Array(4);
  /**
   * A buffer holding the data until the whole block can be processed.
   * @type {!Array<number>}
   * @private
   */
  this.block_ = new Array(this.blockSize);
  /**
   * The length of yet-unprocessed data as collected in the block.
   * @type {number}
   * @private
   */
  this.blockLength_ = 0;
  /**
   * The total length of the message so far.
   * @type {number}
   * @private
   */
  this.totalLength_ = 0;
  this.reset();
};
goog.inherits(goog.crypt.Md5, goog.crypt.Hash);
/**
 * Integer rotation constants used by the abbreviated implementation.
 * They are hardcoded in the unrolled implementation, so it is left
 * here commented out.
 * @type {Array<number>}
 * @private
 *
goog.crypt.Md5.S_ = [
  7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22,
  5, 9, 14, 20, 5, 9, 14, 20, 5, 9, 14, 20, 5, 9, 14, 20,
  4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23,
  6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21
];
 */
/**
 * Sine function constants used by the abbreviated implementation.
 * They are hardcoded in the unrolled implementation, so it is left
 * here commented out.
 * @type {Array<number>}
 * @private
 *
goog.crypt.Md5.T_ = [
  0xd76aa478, 0xe8c7b756, 0x242070db, 0xc1bdceee,
  0xf57c0faf, 0x4787c62a, 0xa8304613, 0xfd469501,
  0x698098d8, 0x8b44f7af, 0xffff5bb1, 0x895cd7be,
  0x6b901122, 0xfd987193, 0xa679438e, 0x49b40821,
  0xf61e2562, 0xc040b340, 0x265e5a51, 0xe9b6c7aa,
  0xd62f105d, 0x02441453, 0xd8a1e681, 0xe7d3fbc8,
  0x21e1cde6, 0xc33707d6, 0xf4d50d87, 0x455a14ed,
  0xa9e3e905, 0xfcefa3f8, 0x676f02d9, 0x8d2a4c8a,
  0xfffa3942, 0x8771f681, 0x6d9d6122, 0xfde5380c,
  0xa4beea44, 0x4bdecfa9, 0xf6bb4b60, 0xbebfbc70,
  0x289b7ec6, 0xeaa127fa, 0xd4ef3085, 0x04881d05,
  0xd9d4d039, 0xe6db99e5, 0x1fa27cf8, 0xc4ac5665,
  0xf4292244, 0x432aff97, 0xab9423a7, 0xfc93a039,
  0x655b59c3, 0x8f0ccc92, 0xffeff47d, 0x85845dd1,
  0x6fa87e4f, 0xfe2ce6e0, 0xa3014314, 0x4e0811a1,
  0xf7537e82, 0xbd3af235, 0x2ad7d2bb, 0xeb86d391
];
 */
/** @override */
goog.crypt.Md5.prototype.reset = function() {
  this.chain_[0] = 0x67452301;
  this.chain_[1] = 0xefcdab89;
  this.chain_[2] = 0x98badcfe;
  this.chain_[3] = 0x10325476;
  this.blockLength_ = 0;
  this.totalLength_ = 0;
};
/**
 * Internal compress helper function. It takes a block of data (64 bytes)
 * and updates the accumulator.
 * @param {Array<number>|Uint8Array|string} buf The block to compress.
 * @param {number=} opt_offset Offset of the block in the buffer.
 * @private
 */
goog.crypt.Md5.prototype.compress_ = function(buf, opt_offset) {
  if (!opt_offset) {
    opt_offset = 0;
  }
  // We allocate the array every time, but it's cheap in practice.
  var X = new Array(16);
  // Get 16 little endian words. It is not worth unrolling this for Chrome 11.
  if (goog.isString(buf)) {
    for (var i = 0; i < 16; ++i) {
      X[i] = (buf.charCodeAt(opt_offset++)) |
             (buf.charCodeAt(opt_offset++) << 8) |
             (buf.charCodeAt(opt_offset++) << 16) |
             (buf.charCodeAt(opt_offset++) << 24);
    }
  } else {
    for (var i = 0; i < 16; ++i) {
      X[i] = (buf[opt_offset++]) |
             (buf[opt_offset++] << 8) |
             (buf[opt_offset++] << 16) |
             (buf[opt_offset++] << 24);
    }
  }
  var A = this.chain_[0];
  var B = this.chain_[1];
  var C = this.chain_[2];
  var D = this.chain_[3];
  var sum = 0;
  /*
   * This is an abbreviated implementation, it is left here commented out for
   * reference purposes. See below for an unrolled version in use.
   *
  var f, n, tmp;
  for (var i = 0; i < 64; ++i) {

    if (i < 16) {
      f = (D ^ (B & (C ^ D)));
      n = i;
    } else if (i < 32) {
      f = (C ^ (D & (B ^ C)));
      n = (5 * i + 1) % 16;
    } else if (i < 48) {
      f = (B ^ C ^ D);
      n = (3 * i + 5) % 16;
    } else {
      f = (C ^ (B | (~D)));
      n = (7 * i) % 16;
    }

    tmp = D;
    D = C;
    C = B;
    sum = (A + f + goog.crypt.Md5.T_[i] + X[n]) & 0xffffffff;
    B += ((sum << goog.crypt.Md5.S_[i]) & 0xffffffff) |
         (sum >>> (32 - goog.crypt.Md5.S_[i]));
    A = tmp;
  }
   */
  /*
   * This is an unrolled MD5 implementation, which gives ~30% speedup compared
   * to the abbreviated implementation above, as measured on Chrome 11. It is
   * important to keep 32-bit croppings to minimum and inline the integer
   * rotation.
   */
  sum = (A + (D ^ (B & (C ^ D))) + X[0] + 0xd76aa478) & 0xffffffff;
  A = B + (((sum << 7) & 0xffffffff) | (sum >>> 25));
  sum = (D + (C ^ (A & (B ^ C))) + X[1] + 0xe8c7b756) & 0xffffffff;
  D = A + (((sum << 12) & 0xffffffff) | (sum >>> 20));
  sum = (C + (B ^ (D & (A ^ B))) + X[2] + 0x242070db) & 0xffffffff;
  C = D + (((sum << 17) & 0xffffffff) | (sum >>> 15));
  sum = (B + (A ^ (C & (D ^ A))) + X[3] + 0xc1bdceee) & 0xffffffff;
  B = C + (((sum << 22) & 0xffffffff) | (sum >>> 10));
  sum = (A + (D ^ (B & (C ^ D))) + X[4] + 0xf57c0faf) & 0xffffffff;
  A = B + (((sum << 7) & 0xffffffff) | (sum >>> 25));
  sum = (D + (C ^ (A & (B ^ C))) + X[5] + 0x4787c62a) & 0xffffffff;
  D = A + (((sum << 12) & 0xffffffff) | (sum >>> 20));
  sum = (C + (B ^ (D & (A ^ B))) + X[6] + 0xa8304613) & 0xffffffff;
  C = D + (((sum << 17) & 0xffffffff) | (sum >>> 15));
  sum = (B + (A ^ (C & (D ^ A))) + X[7] + 0xfd469501) & 0xffffffff;
  B = C + (((sum << 22) & 0xffffffff) | (sum >>> 10));
  sum = (A + (D ^ (B & (C ^ D))) + X[8] + 0x698098d8) & 0xffffffff;
  A = B + (((sum << 7) & 0xffffffff) | (sum >>> 25));
  sum = (D + (C ^ (A & (B ^ C))) + X[9] + 0x8b44f7af) & 0xffffffff;
  D = A + (((sum << 12) & 0xffffffff) | (sum >>> 20));
  sum = (C + (B ^ (D & (A ^ B))) + X[10] + 0xffff5bb1) & 0xffffffff;
  C = D + (((sum << 17) & 0xffffffff) | (sum >>> 15));
  sum = (B + (A ^ (C & (D ^ A))) + X[11] + 0x895cd7be) & 0xffffffff;
  B = C + (((sum << 22) & 0xffffffff) | (sum >>> 10));
  sum = (A + (D ^ (B & (C ^ D))) + X[12] + 0x6b901122) & 0xffffffff;
  A = B + (((sum << 7) & 0xffffffff) | (sum >>> 25));
  sum = (D + (C ^ (A & (B ^ C))) + X[13] + 0xfd987193) & 0xffffffff;
  D = A + (((sum << 12) & 0xffffffff) | (sum >>> 20));
  sum = (C + (B ^ (D & (A ^ B))) + X[14] + 0xa679438e) & 0xffffffff;
  C = D + (((sum << 17) & 0xffffffff) | (sum >>> 15));
  sum = (B + (A ^ (C & (D ^ A))) + X[15] + 0x49b40821) & 0xffffffff;
  B = C + (((sum << 22) & 0xffffffff) | (sum >>> 10));
  sum = (A + (C ^ (D & (B ^ C))) + X[1] + 0xf61e2562) & 0xffffffff;
  A = B + (((sum << 5) & 0xffffffff) | (sum >>> 27));
  sum = (D + (B ^ (C & (A ^ B))) + X[6] + 0xc040b340) & 0xffffffff;
  D = A + (((sum << 9) & 0xffffffff) | (sum >>> 23));
  sum = (C + (A ^ (B & (D ^ A))) + X[11] + 0x265e5a51) & 0xffffffff;
  C = D + (((sum << 14) & 0xffffffff) | (sum >>> 18));
  sum = (B + (D ^ (A & (C ^ D))) + X[0] + 0xe9b6c7aa) & 0xffffffff;
  B = C + (((sum << 20) & 0xffffffff) | (sum >>> 12));
  sum = (A + (C ^ (D & (B ^ C))) + X[5] + 0xd62f105d) & 0xffffffff;
  A = B + (((sum << 5) & 0xffffffff) | (sum >>> 27));
  sum = (D + (B ^ (C & (A ^ B))) + X[10] + 0x02441453) & 0xffffffff;
  D = A + (((sum << 9) & 0xffffffff) | (sum >>> 23));
  sum = (C + (A ^ (B & (D ^ A))) + X[15] + 0xd8a1e681) & 0xffffffff;
  C = D + (((sum << 14) & 0xffffffff) | (sum >>> 18));
  sum = (B + (D ^ (A & (C ^ D))) + X[4] + 0xe7d3fbc8) & 0xffffffff;
  B = C + (((sum << 20) & 0xffffffff) | (sum >>> 12));
  sum = (A + (C ^ (D & (B ^ C))) + X[9] + 0x21e1cde6) & 0xffffffff;
  A = B + (((sum << 5) & 0xffffffff) | (sum >>> 27));
  sum = (D + (B ^ (C & (A ^ B))) + X[14] + 0xc33707d6) & 0xffffffff;
  D = A + (((sum << 9) & 0xffffffff) | (sum >>> 23));
  sum = (C + (A ^ (B & (D ^ A))) + X[3] + 0xf4d50d87) & 0xffffffff;
  C = D + (((sum << 14) & 0xffffffff) | (sum >>> 18));
  sum = (B + (D ^ (A & (C ^ D))) + X[8] + 0x455a14ed) & 0xffffffff;
  B = C + (((sum << 20) & 0xffffffff) | (sum >>> 12));
  sum = (A + (C ^ (D & (B ^ C))) + X[13] + 0xa9e3e905) & 0xffffffff;
  A = B + (((sum << 5) & 0xffffffff) | (sum >>> 27));
  sum = (D + (B ^ (C & (A ^ B))) + X[2] + 0xfcefa3f8) & 0xffffffff;
  D = A + (((sum << 9) & 0xffffffff) | (sum >>> 23));
  sum = (C + (A ^ (B & (D ^ A))) + X[7] + 0x676f02d9) & 0xffffffff;
  C = D + (((sum << 14) & 0xffffffff) | (sum >>> 18));
  sum = (B + (D ^ (A & (C ^ D))) + X[12] + 0x8d2a4c8a) & 0xffffffff;
  B = C + (((sum << 20) & 0xffffffff) | (sum >>> 12));
  sum = (A + (B ^ C ^ D) + X[5] + 0xfffa3942) & 0xffffffff;
  A = B + (((sum << 4) & 0xffffffff) | (sum >>> 28));
  sum = (D + (A ^ B ^ C) + X[8] + 0x8771f681) & 0xffffffff;
  D = A + (((sum << 11) & 0xffffffff) | (sum >>> 21));
  sum = (C + (D ^ A ^ B) + X[11] + 0x6d9d6122) & 0xffffffff;
  C = D + (((sum << 16) & 0xffffffff) | (sum >>> 16));
  sum = (B + (C ^ D ^ A) + X[14] + 0xfde5380c) & 0xffffffff;
  B = C + (((sum << 23) & 0xffffffff) | (sum >>> 9));
  sum = (A + (B ^ C ^ D) + X[1] + 0xa4beea44) & 0xffffffff;
  A = B + (((sum << 4) & 0xffffffff) | (sum >>> 28));
  sum = (D + (A ^ B ^ C) + X[4] + 0x4bdecfa9) & 0xffffffff;
  D = A + (((sum << 11) & 0xffffffff) | (sum >>> 21));
  sum = (C + (D ^ A ^ B) + X[7] + 0xf6bb4b60) & 0xffffffff;
  C = D + (((sum << 16) & 0xffffffff) | (sum >>> 16));
  sum = (B + (C ^ D ^ A) + X[10] + 0xbebfbc70) & 0xffffffff;
  B = C + (((sum << 23) & 0xffffffff) | (sum >>> 9));
  sum = (A + (B ^ C ^ D) + X[13] + 0x289b7ec6) & 0xffffffff;
  A = B + (((sum << 4) & 0xffffffff) | (sum >>> 28));
  sum = (D + (A ^ B ^ C) + X[0] + 0xeaa127fa) & 0xffffffff;
  D = A + (((sum << 11) & 0xffffffff) | (sum >>> 21));
  sum = (C + (D ^ A ^ B) + X[3] + 0xd4ef3085) & 0xffffffff;
  C = D + (((sum << 16) & 0xffffffff) | (sum >>> 16));
  sum = (B + (C ^ D ^ A) + X[6] + 0x04881d05) & 0xffffffff;
  B = C + (((sum << 23) & 0xffffffff) | (sum >>> 9));
  sum = (A + (B ^ C ^ D) + X[9] + 0xd9d4d039) & 0xffffffff;
  A = B + (((sum << 4) & 0xffffffff) | (sum >>> 28));
  sum = (D + (A ^ B ^ C) + X[12] + 0xe6db99e5) & 0xffffffff;
  D = A + (((sum << 11) & 0xffffffff) | (sum >>> 21));
  sum = (C + (D ^ A ^ B) + X[15] + 0x1fa27cf8) & 0xffffffff;
  C = D + (((sum << 16) & 0xffffffff) | (sum >>> 16));
  sum = (B + (C ^ D ^ A) + X[2] + 0xc4ac5665) & 0xffffffff;
  B = C + (((sum << 23) & 0xffffffff) | (sum >>> 9));
  sum = (A + (C ^ (B | (~D))) + X[0] + 0xf4292244) & 0xffffffff;
  A = B + (((sum << 6) & 0xffffffff) | (sum >>> 26));
  sum = (D + (B ^ (A | (~C))) + X[7] + 0x432aff97) & 0xffffffff;
  D = A + (((sum << 10) & 0xffffffff) | (sum >>> 22));
  sum = (C + (A ^ (D | (~B))) + X[14] + 0xab9423a7) & 0xffffffff;
  C = D + (((sum << 15) & 0xffffffff) | (sum >>> 17));
  sum = (B + (D ^ (C | (~A))) + X[5] + 0xfc93a039) & 0xffffffff;
  B = C + (((sum << 21) & 0xffffffff) | (sum >>> 11));
  sum = (A + (C ^ (B | (~D))) + X[12] + 0x655b59c3) & 0xffffffff;
  A = B + (((sum << 6) & 0xffffffff) | (sum >>> 26));
  sum = (D + (B ^ (A | (~C))) + X[3] + 0x8f0ccc92) & 0xffffffff;
  D = A + (((sum << 10) & 0xffffffff) | (sum >>> 22));
  sum = (C + (A ^ (D | (~B))) + X[10] + 0xffeff47d) & 0xffffffff;
  C = D + (((sum << 15) & 0xffffffff) | (sum >>> 17));
  sum = (B + (D ^ (C | (~A))) + X[1] + 0x85845dd1) & 0xffffffff;
  B = C + (((sum << 21) & 0xffffffff) | (sum >>> 11));
  sum = (A + (C ^ (B | (~D))) + X[8] + 0x6fa87e4f) & 0xffffffff;
  A = B + (((sum << 6) & 0xffffffff) | (sum >>> 26));
  sum = (D + (B ^ (A | (~C))) + X[15] + 0xfe2ce6e0) & 0xffffffff;
  D = A + (((sum << 10) & 0xffffffff) | (sum >>> 22));
  sum = (C + (A ^ (D | (~B))) + X[6] + 0xa3014314) & 0xffffffff;
  C = D + (((sum << 15) & 0xffffffff) | (sum >>> 17));
  sum = (B + (D ^ (C | (~A))) + X[13] + 0x4e0811a1) & 0xffffffff;
  B = C + (((sum << 21) & 0xffffffff) | (sum >>> 11));
  sum = (A + (C ^ (B | (~D))) + X[4] + 0xf7537e82) & 0xffffffff;
  A = B + (((sum << 6) & 0xffffffff) | (sum >>> 26));
  sum = (D + (B ^ (A | (~C))) + X[11] + 0xbd3af235) & 0xffffffff;
  D = A + (((sum << 10) & 0xffffffff) | (sum >>> 22));
  sum = (C + (A ^ (D | (~B))) + X[2] + 0x2ad7d2bb) & 0xffffffff;
  C = D + (((sum << 15) & 0xffffffff) | (sum >>> 17));
  sum = (B + (D ^ (C | (~A))) + X[9] + 0xeb86d391) & 0xffffffff;
  B = C + (((sum << 21) & 0xffffffff) | (sum >>> 11));
  this.chain_[0] = (this.chain_[0] + A) & 0xffffffff;
  this.chain_[1] = (this.chain_[1] + B) & 0xffffffff;
  this.chain_[2] = (this.chain_[2] + C) & 0xffffffff;
  this.chain_[3] = (this.chain_[3] + D) & 0xffffffff;
};
/** @override */
goog.crypt.Md5.prototype.update = function(bytes, opt_length) {
  if (!goog.isDef(opt_length)) {
    opt_length = bytes.length;
  }
  var lengthMinusBlock = opt_length - this.blockSize;
  // Copy some object properties to local variables in order to save on access
  // time from inside the loop (~10% speedup was observed on Chrome 11).
  var block = this.block_;
  var blockLength = this.blockLength_;
  var i = 0;
  // The outer while loop should execute at most twice.
  while (i < opt_length) {
    // When we have no data in the block to top up, we can directly process the
    // input buffer (assuming it contains sufficient data). This gives ~30%
    // speedup on Chrome 14 and ~70% speedup on Firefox 6.0, but requires that
    // the data is provided in large chunks (or in multiples of 64 bytes).
    if (blockLength == 0) {
      while (i <= lengthMinusBlock) {
        this.compress_(bytes, i);
        i += this.blockSize;
      }
    }
    if (goog.isString(bytes)) {
      while (i < opt_length) {
        block[blockLength++] = bytes.charCodeAt(i++);
        if (blockLength == this.blockSize) {
          this.compress_(block);
          blockLength = 0;
          // Jump to the outer loop so we use the full-block optimization.
          break;
        }
      }
    } else {
      while (i < opt_length) {
        block[blockLength++] = bytes[i++];
        if (blockLength == this.blockSize) {
          this.compress_(block);
          blockLength = 0;
          // Jump to the outer loop so we use the full-block optimization.
          break;
        }
      }
    }
  }
  this.blockLength_ = blockLength;
  this.totalLength_ += opt_length;
};
/** @override */
goog.crypt.Md5.prototype.digest = function() {
  // This must accommodate at least 1 padding byte (0x80), 8 bytes of
  // total bitlength, and must end at a 64-byte boundary.
  var pad = new Array((this.blockLength_ < 56 ?
                       this.blockSize :
                       this.blockSize * 2) - this.blockLength_);
  // Add padding: 0x80 0x00*
  pad[0] = 0x80;
  for (var i = 1; i < pad.length - 8; ++i) {
    pad[i] = 0;
  }
  // Add the total number of bits, little endian 64-bit integer.
  var totalBits = this.totalLength_ * 8;
  for (var i = pad.length - 8; i < pad.length; ++i) {
    pad[i] = totalBits & 0xff;
    totalBits /= 0x100; // Don't use bit-shifting here!
  }
  this.update(pad);
  var digest = new Array(16);
  var n = 0;
  for (var i = 0; i < 4; ++i) {
    for (var j = 0; j < 32; j += 8) {
      digest[n++] = (this.chain_[i] >>> j) & 0xff;
    }
  }
  return digest;
};
/* Copyright (C) 1991-2017 Free Software Foundation, Inc.
   This file is part of the GNU C Library.

   The GNU C Library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2.1 of the License, or (at your option) any later version.

   The GNU C Library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public
   License along with the GNU C Library; if not, see
   <http://www.gnu.org/licenses/>.  */
/* This header is separate from features.h so that the compiler can
   include it implicitly at the start of every compilation.  It must
   not itself include <features.h> or any other header that includes
   <features.h> because the implicit include comes before any feature
   test macros that may be defined in a source file before it first
   explicitly includes a system header.  GCC knows the name of this
   header in order to preinclude it.  */
/* glibc's intent is to support the IEC 559 math functionality, real
   and complex.  If the GCC (4.9 and later) predefined macros
   specifying compiler intent are available, use them to determine
   whether the overall intent is to support these features; otherwise,
   presume an older compiler has intent to support these features and
   define these macros by default.  */
/* wchar_t uses Unicode 8.0.0.  Version 8.0 of the Unicode Standard is
   synchronized with ISO/IEC 10646:2014, plus Amendment 1 (published
   2015-05-15).  */
/* We do not support C11 <threads.h>.  */
/* include/HsBaseConfig.h.  Generated from HsBaseConfig.h.in by configure.  */
/* include/HsBaseConfig.h.in.  Generated from configure.ac by autoheader.  */
/* The value of E2BIG. */
/* The value of EACCES. */
/* The value of EADDRINUSE. */
/* The value of EADDRNOTAVAIL. */
/* The value of EADV. */
/* The value of EAFNOSUPPORT. */
/* The value of EAGAIN. */
/* The value of EALREADY. */
/* The value of EBADF. */
/* The value of EBADMSG. */
/* The value of EBADRPC. */
/* The value of EBUSY. */
/* The value of ECHILD. */
/* The value of ECOMM. */
/* The value of ECONNABORTED. */
/* The value of ECONNREFUSED. */
/* The value of ECONNRESET. */
/* The value of EDEADLK. */
/* The value of EDESTADDRREQ. */
/* The value of EDIRTY. */
/* The value of EDOM. */
/* The value of EDQUOT. */
/* The value of EEXIST. */
/* The value of EFAULT. */
/* The value of EFBIG. */
/* The value of EFTYPE. */
/* The value of EHOSTDOWN. */
/* The value of EHOSTUNREACH. */
/* The value of EIDRM. */
/* The value of EILSEQ. */
/* The value of EINPROGRESS. */
/* The value of EINTR. */
/* The value of EINVAL. */
/* The value of EIO. */
/* The value of EISCONN. */
/* The value of EISDIR. */
/* The value of ELOOP. */
/* The value of EMFILE. */
/* The value of EMLINK. */
/* The value of EMSGSIZE. */
/* The value of EMULTIHOP. */
/* The value of ENAMETOOLONG. */
/* The value of ENETDOWN. */
/* The value of ENETRESET. */
/* The value of ENETUNREACH. */
/* The value of ENFILE. */
/* The value of ENOBUFS. */
/* The value of ENOCIGAR. */
/* The value of ENODATA. */
/* The value of ENODEV. */
/* The value of ENOENT. */
/* The value of ENOEXEC. */
/* The value of ENOLCK. */
/* The value of ENOLINK. */
/* The value of ENOMEM. */
/* The value of ENOMSG. */
/* The value of ENONET. */
/* The value of ENOPROTOOPT. */
/* The value of ENOSPC. */
/* The value of ENOSR. */
/* The value of ENOSTR. */
/* The value of ENOSYS. */
/* The value of ENOTBLK. */
/* The value of ENOTCONN. */
/* The value of ENOTDIR. */
/* The value of ENOTEMPTY. */
/* The value of ENOTSOCK. */
/* The value of ENOTSUP. */
/* The value of ENOTTY. */
/* The value of ENXIO. */
/* The value of EOPNOTSUPP. */
/* The value of EPERM. */
/* The value of EPFNOSUPPORT. */
/* The value of EPIPE. */
/* The value of EPROCLIM. */
/* The value of EPROCUNAVAIL. */
/* The value of EPROGMISMATCH. */
/* The value of EPROGUNAVAIL. */
/* The value of EPROTO. */
/* The value of EPROTONOSUPPORT. */
/* The value of EPROTOTYPE. */
/* The value of ERANGE. */
/* The value of EREMCHG. */
/* The value of EREMOTE. */
/* The value of EROFS. */
/* The value of ERPCMISMATCH. */
/* The value of ERREMOTE. */
/* The value of ESHUTDOWN. */
/* The value of ESOCKTNOSUPPORT. */
/* The value of ESPIPE. */
/* The value of ESRCH. */
/* The value of ESRMNT. */
/* The value of ESTALE. */
/* The value of ETIME. */
/* The value of ETIMEDOUT. */
/* The value of ETOOMANYREFS. */
/* The value of ETXTBSY. */
/* The value of EUSERS. */
/* The value of EWOULDBLOCK. */
/* The value of EXDEV. */
/* The value of O_BINARY. */
/* The value of SIGINT. */
/* Define to 1 if you have the `clock_gettime' function. */
/* #undef HAVE_CLOCK_GETTIME */
/* Define to 1 if you have the <ctype.h> header file. */
/* Define if you have epoll support. */
/* #undef HAVE_EPOLL */
/* Define to 1 if you have the `epoll_ctl' function. */
/* #undef HAVE_EPOLL_CTL */
/* Define to 1 if you have the <errno.h> header file. */
/* Define to 1 if you have the `eventfd' function. */
/* #undef HAVE_EVENTFD */
/* Define to 1 if you have the <fcntl.h> header file. */
/* Define to 1 if you have the `ftruncate' function. */
/* Define to 1 if you have the `getclock' function. */
/* #undef HAVE_GETCLOCK */
/* Define to 1 if you have the `getrusage' function. */
/* Define to 1 if you have the <inttypes.h> header file. */
/* Define to 1 if you have the `iswspace' function. */
/* Define to 1 if you have the `kevent' function. */
/* Define to 1 if you have the `kevent64' function. */
/* Define if you have kqueue support. */
/* Define to 1 if you have the <langinfo.h> header file. */
/* Define to 1 if you have libcharset. */
/* Define to 1 if you have the `rt' library (-lrt). */
/* #undef HAVE_LIBRT */
/* Define to 1 if you have the <limits.h> header file. */
/* Define to 1 if the system has the type `long long'. */
/* Define to 1 if you have the `lstat' function. */
/* Define to 1 if you have the <memory.h> header file. */
/* Define if you have poll support. */
/* Define to 1 if you have the <poll.h> header file. */
/* Define to 1 if you have the <signal.h> header file. */
/* Define to 1 if you have the <stdint.h> header file. */
/* Define to 1 if you have the <stdlib.h> header file. */
/* Define to 1 if you have the <strings.h> header file. */
/* Define to 1 if you have the <string.h> header file. */
/* Define to 1 if you have the <sys/epoll.h> header file. */
/* #undef HAVE_SYS_EPOLL_H */
/* Define to 1 if you have the <sys/eventfd.h> header file. */
/* #undef HAVE_SYS_EVENTFD_H */
/* Define to 1 if you have the <sys/event.h> header file. */
/* Define to 1 if you have the <sys/resource.h> header file. */
/* Define to 1 if you have the <sys/select.h> header file. */
/* Define to 1 if you have the <sys/stat.h> header file. */
/* Define to 1 if you have the <sys/syscall.h> header file. */
/* Define to 1 if you have the <sys/timeb.h> header file. */
/* Define to 1 if you have the <sys/timers.h> header file. */
/* #undef HAVE_SYS_TIMERS_H */
/* Define to 1 if you have the <sys/times.h> header file. */
/* Define to 1 if you have the <sys/time.h> header file. */
/* Define to 1 if you have the <sys/types.h> header file. */
/* Define to 1 if you have the <sys/utsname.h> header file. */
/* Define to 1 if you have the <sys/wait.h> header file. */
/* Define to 1 if you have the <termios.h> header file. */
/* Define to 1 if you have the `times' function. */
/* Define to 1 if you have the <time.h> header file. */
/* Define to 1 if you have the <unistd.h> header file. */
/* Define to 1 if you have the <utime.h> header file. */
/* Define to 1 if you have the <wctype.h> header file. */
/* Define to 1 if you have the <windows.h> header file. */
/* #undef HAVE_WINDOWS_H */
/* Define to 1 if you have the <winsock.h> header file. */
/* #undef HAVE_WINSOCK_H */
/* Define to 1 if you have the `_chsize' function. */
/* #undef HAVE__CHSIZE */
/* Define to Haskell type for cc_t */
/* Define to Haskell type for char */
/* Define to Haskell type for clock_t */
/* Define to Haskell type for dev_t */
/* Define to Haskell type for double */
/* Define to Haskell type for float */
/* Define to Haskell type for gid_t */
/* Define to Haskell type for ino_t */
/* Define to Haskell type for int */
/* Define to Haskell type for intmax_t */
/* Define to Haskell type for intptr_t */
/* Define to Haskell type for long */
/* Define to Haskell type for long long */
/* Define to Haskell type for mode_t */
/* Define to Haskell type for nlink_t */
/* Define to Haskell type for off_t */
/* Define to Haskell type for pid_t */
/* Define to Haskell type for ptrdiff_t */
/* Define to Haskell type for rlim_t */
/* Define to Haskell type for short */
/* Define to Haskell type for signed char */
/* Define to Haskell type for sig_atomic_t */
/* Define to Haskell type for size_t */
/* Define to Haskell type for speed_t */
/* Define to Haskell type for ssize_t */
/* Define to Haskell type for suseconds_t */
/* Define to Haskell type for tcflag_t */
/* Define to Haskell type for time_t */
/* Define to Haskell type for uid_t */
/* Define to Haskell type for uintmax_t */
/* Define to Haskell type for uintptr_t */
/* Define to Haskell type for unsigned char */
/* Define to Haskell type for unsigned int */
/* Define to Haskell type for unsigned long */
/* Define to Haskell type for unsigned long long */
/* Define to Haskell type for unsigned short */
/* Define to Haskell type for useconds_t */
/* Define to Haskell type for wchar_t */
/* Define to the address where bug reports for this package should be sent. */
/* Define to the full name of this package. */
/* Define to the full name and version of this package. */
/* Define to the one symbol short name of this package. */
/* Define to the home page for this package. */
/* Define to the version of this package. */
/* The size of `kev.filter', as computed by sizeof. */
/* The size of `kev.flags', as computed by sizeof. */
/* The size of `struct MD5Context', as computed by sizeof. */
/* Define to 1 if you have the ANSI C header files. */
/* Number of bits in a file offset, on hosts where this is settable. */
/* #undef _FILE_OFFSET_BITS */
/* Define for large files, on AIX-style hosts. */
/* #undef _LARGE_FILES */
// values defined in Gen2.ClosureInfo
// thread status
/*
 * low-level heap object manipulation macros
 */
// GHCJS.Prim.JSVal
// GHCJS.Prim.JSException
// Exception dictionary for JSException
// SomeException
// GHC.Ptr.Ptr
// GHC.Integer.GMP.Internals
// Data.Maybe.Maybe
// #define HS_NOTHING h$nothing
// Data.List
// Data.Text
// Data.Text.Lazy
// black holes
// can we skip the indirection for black holes?
// resumable thunks
// general deconstruction
// retrieve  a numeric value that's possibly stored as an indirection
// generic lazy values
// generic data constructors and selectors
// unboxed tuple returns
// #define RETURN_UBX_TUP1(x) return x;
// #define GHCJS_TRACE_IO 1
function h$base_access(file, file_off, mode, c) {
    ;
    if(h$isNode) {
        h$fs.stat(fd, function(err, fs) {
            if(err) {
                h$handleErrnoC(err, -1, 0, c);
            } else {
                c(mode & fs.mode); // fixme is this ok?
            }
        });
    } else
        h$unsupported(-1, c);
}
function h$base_chmod(file, file_off, mode, c) {
    ;
    if(h$isNode) {
        h$fs.chmod(h$decodeUtf8z(file, file_off), mode, function(err) {
            h$handleErrnoC(err, -1, 0, c);
        });
    } else
        h$unsupported(-1, c);
}
function h$base_close(fd, c) {
    ;
    var fdo = h$base_fds[fd];
    if(fdo && fdo.close) {
        fdo.close(fd, fdo, c);
    } else {
        h$errno = 22;
        c(-1);
    }
}
function h$base_dup(fd, something, c) {
    throw "h$base_dup";
}
function h$base_dup2(fd, c) {
    throw "h$base_dup2";
}
function h$base_fstat(fd, stat, stat_off, c) {
    ;
    if(h$isNode) {
        h$fs.fstat(fd, function(err, fs) {
            if(err) {
                h$handlErrnoC(err, -1, 0, c);
            } else {
                h$base_fillStat(fs, stat, stat_off);
                c(0);
            }
        });
    } else
        h$unsupported(-1, c);
}
function h$base_isatty(fd) {
    ;
    if(h$isNode) {
        if(fd === 0) return process.stdin.isTTY?1:0;
        if(fd === 1) return process.stdout.isTTY?1:0;
        if(fd === 2) return process.stderr.isTTY?1:0;
    }
    if(fd === 1 || fd === 2) return 1;
    return 0;
}
function h$base_lseek(fd, pos_1, pos_2, whence, c) {
    ;
    if(h$isNode) {
        var p = goog.math.Long.fromBits(pos_2, pos_1), p1;
        var o = h$base_fds[fd];
        if(!o) {
            h$errno = CONST_BADF;
            c(-1,-1);
        } else {
            switch(whence) {
            case 0: /* SET */
                o.pos = p.toNumber();
                c(p.getHighBits(), p.getLowBits());
                break;
            case 1: /* CUR */
                o.pos += p.toNumber();
                p1 = goog.math.Long.fromNumber(o.pos);
                c(p1.getHighBits(), p1.getLowBits());
                break;
            case 2: /* END */
                h$fs.fstat(fd, function(err, fs) {
                    if(err) {
                        h$setErrno(err);
                        c(-1,-1);
                    } else {
                        o.pos = fs.size + p.toNumber();
                        p1 = goog.math.Long.fromNumber(o.pos);
                        c(p1.getHighBits(), p1.getLowBits());
                    }
                });
                break;
            default:
                h$errno = 22;
                c(-1,-1);
            }
        }
    } else {
        h$unsupported();
        c(-1, -1);
    }
}
function h$base_lstat(file, file_off, stat, stat_off, c) {
    ;
    if(h$isNode) {
        h$fs.lstat(h$decodeUtf8z(file, file_off), function(err, fs) {
            if(err) {
                h$handleErrnoC(err, -1, 0, c);
            } else {
                h$base_fillStat(fs, stat, stat_off);
                c(0);
            }
        });
    } else
        h$unsupported(-1, c);
}
function h$base_open(file, file_off, how, mode, c) {
    if(h$isNode) {
        var flags, off;
        var fp = h$decodeUtf8z(file, file_off);
        var acc = how & h$base_o_accmode;
        // passing a number lets node.js use it directly as the flags (undocumented)
        if(acc === h$base_o_rdonly) {
            flags = h$processConstants['fs']['O_RDONLY'];
        } else if(acc === h$base_o_wronly) {
            flags = h$processConstants['fs']['O_WRONLY'];
        } else { // r+w
            flags = h$processConstants['fs']['O_RDWR'];
        }
        off = (how & h$base_o_append) ? -1 : 0;
        flags = flags | ((how & h$base_o_trunc) ? h$processConstants['fs']['O_TRUNC'] : 0)
                      | ((how & h$base_o_creat) ? h$processConstants['fs']['O_CREAT'] : 0)
                      | ((how & h$base_o_excl) ? h$processConstants['fs']['O_EXCL'] : 0)
                      | ((how & h$base_o_append) ? h$processConstants['fs']['O_APPEND'] : 0);
        h$fs.open(fp, flags, mode, function(err, fd) {
            if(err) {
                h$handleErrnoC(err, -1, 0, c);
            } else {
                var f = function(p) {
                    h$base_fds[fd] = { read: h$base_readFile
                                       , write: h$base_writeFile
                                       , close: h$base_closeFile
                                       , pos: p
                                     };
                    c(fd);
                }
                if(off === -1) {
                    h$fs.stat(fp, function(err, fs) {
                        if(err) h$handleErrnoC(err, -1, 0, c); else f(fs.size);
                    });
                } else {
                    f(0);
                }
            }
        });
    } else
        h$unsupported(-1, c);
}
function h$base_read(fd, buf, buf_off, n, c) {
    ;
    var fdo = h$base_fds[fd];
    if(fdo && fdo.read) {
        fdo.read(fd, fdo, buf, buf_off, n, c);
    } else {
        h$errno = 22;
        c(-1);
    }
}
function h$base_stat(file, file_off, stat, stat_off, c) {
    ;
    if(h$isNode) {
        h$fs.stat(h$decodeUtf8z(file, file_off), function(err, fs) {
            if(err) {
                h$handlErrnoC(err, -1, 0, c);
            } else {
                h$base_fillStat(fs, stat, stat_off);
                c(0);
            }
        });
    } else
        h$unsupported(-1, c);
}
function h$base_umask(mode) {
    ;
    if(h$isNode) return process.umask(mode);
    return 0;
}
function h$base_write(fd, buf, buf_off, n, c) {
    ;
    var fdo = h$base_fds[fd];
    if(fdo && fdo.write) {
        fdo.write(fd, fdo, buf, buf_off, n, c);
    } else {
        h$errno = 22;
        c(-1);
    }
}
function h$base_ftruncate(fd, pos_1, pos_2, c) {
    ;
    if(h$isNode) {
        h$fs.ftruncate(fd, goog.math.Long.fromBits(pos_2, pos_1).toNumber(), function(err) {
            h$handleErrnoC(err, -1, 0, c);
        });
    } else
        h$unsupported(-1, c);
}
function h$base_unlink(file, file_off, c) {
    ;
    if(h$isNode) {
        h$fs.unlink(h$decodeUtf8z(file, file_off), function(err) {
            h$handleErrnoC(err, -1, 0, c);
        });
    } else
        h$unsupported(-1, c);
}
function h$base_getpid() {
    ;
    if(h$isNode) return process.pid;
    return 0;
}
function h$base_link(file1, file1_off, file2, file2_off, c) {
    ;
    if(h$isNode) {
        h$fs.link(h$decodeUtf8z(file1, file1_off), h$decodeUtf8z(file2, file2_off), function(err) {
            h$handleErrnoC(err, -1, 0, c);
        });
    } else
        h$unsupported(-1, c);
}
function h$base_mkfifo(file, file_off, mode, c) {
    throw "h$base_mkfifo";
}
function h$base_sigemptyset(sigset, sigset_off) {
    return 0;
    // throw "h$base_sigemptyset";
}
function h$base_sigaddset(sigset, sigset_off, sig) {
    return 0;
    // throw "h$base_sigaddset";
}
function h$base_sigprocmask(sig, sigset1, sigset1_off, sigset2, sigset2_off) {
    return 0;
    // throw "h$base_sigprocmask";
}
function h$base_tcgetattr(attr, termios, termios_off) {
    return 0;
}
function h$base_tcsetattr(attr, val, termios, termios_off) {
    return 0;
}
function h$base_utime(file, file_off, timbuf, timbuf_off, c) {
    ;
    if(h$isNode) {
        h$fs.fstat(h$decodeUtf8z(file, file_off), function(err, fs) {
            if(err) {
                h$handleErrnoC(err, 0, -1, c); // fixme
            } else {
                var atime = goog.math.Long.fromNumber(fs.atime.getTime());
                var mtime = goog.math.Long.fromNumber(fs.mtime.getTime());
                var ctime = goog.math.Long.fromNumber(fs.ctime.getTime());
                timbuf.i3[0] = atime.getHighBits();
                timbuf.i3[1] = atime.getLowBits();
                timbuf.i3[2] = mtime.getHighBits();
                timbuf.i3[3] = mtime.getLowBits();
                timbuf.i3[4] = ctime.getHighBits();
                timbuf.i3[5] = ctime.getLowBits();
                c(0);
            }
        });
    } else
        h$unsupported(-1, c);
}
function h$base_waitpid(pid, stat, stat_off, options, c) {
    throw "h$base_waitpid";
}
/** @const */ var h$base_o_rdonly = 0x00000;
/** @const */ var h$base_o_wronly = 0x00001;
/** @const */ var h$base_o_rdwr = 0x00002;
/** @const */ var h$base_o_accmode = 0x00003;
/** @const */ var h$base_o_append = 0x00008;
/** @const */ var h$base_o_creat = 0x00200;
/** @const */ var h$base_o_trunc = 0x00400;
/** @const */ var h$base_o_excl = 0x00800;
/** @const */ var h$base_o_noctty = 0x20000;
/** @const */ var h$base_o_nonblock = 0x00004;
/** @const */ var h$base_o_binary = 0x00000;
function h$base_c_s_isreg(mode) {
    return 1;
}
function h$base_c_s_ischr(mode) {
    return 0;
}
function h$base_c_s_isblk(mode) {
    return 0;
}
function h$base_c_s_isdir(mode) {
    return 0; // fixme
}
function h$base_c_s_isfifo(mode) {
    return 0;
}
function h$base_fillStat(fs, b, off) {
    if(off%4) throw "h$base_fillStat: not aligned";
    var o = off>>2;
    b.i3[o+0] = fs.mode;
    var s = goog.math.Long.fromNumber(fs.size);
    b.i3[o+1] = s.getHighBits();
    b.i3[o+2] = s.getLowBits();
    b.i3[o+3] = 0; // fixme
    b.i3[o+4] = 0; // fixme
    b.i3[o+5] = fs.dev;
    var i = goog.math.Long.fromNumber(fs.ino);
    b.i3[o+6] = i.getHighBits();
    b.i3[o+7] = i.getLowBits();
    b.i3[o+8] = fs.uid;
    b.i3[o+9] = fs.gid;
}
// [mode,size1,size2,mtime1,mtime2,dev,ino1,ino2,uid,gid] all 32 bit
/** @const */ var h$base_sizeof_stat = 40;
function h$base_st_mtime(stat, stat_off) {
    { h$ret1 = (stat.i3[(stat_off>>2)+4]); return (stat.i3[(stat_off>>2)+3]); };
}
function h$base_st_size(stat, stat_off) {
    { h$ret1 = (stat.i3[(stat_off>>2)+2]); return (stat.i3[(stat_off>>2)+1]); };
}
function h$base_st_mode(stat, stat_off) {
    return stat.i3[stat_off>>2];
}
function h$base_st_dev(stat, stat_off) {
    return stat.i3[(stat_off>>2)+5];
}
function h$base_st_ino(stat, stat_off) {
    { h$ret1 = (stat.i3[(stat_off>>2)+7]); return (stat.i3[(stat_off>>2)+6]); };
}
/** @const */ var h$base_echo = 1;
/** @const */ var h$base_tcsanow = 2;
/** @const */ var h$base_icanon = 4;
/** @const */ var h$base_vmin = 8;
/** @const */ var h$base_vtime = 16;
/** @const */ var h$base_sigttou = 0;
/** @const */ var h$base_sig_block = 0;
/** @const */ var h$base_sig_setmask = 0;
/** @const */ var h$base_f_getfl = 0;
/** @const */ var h$base_f_setfl = 0;
/** @const */ var h$base_f_setfd = 0;
/** @const */ var h$base_fd_cloexec = 0;
/** @const */ var h$base_sizeof_termios = 4;
/** @const */ var h$base_sizeof_sigset_t = 4;
function h$base_lflag(termios, termios_off) {
    return 0;
}
function h$base_poke_lflag(termios, termios_off, flag) {
    return 0;
}
function h$base_ptr_c_cc(termios, termios_off) {
    { h$ret1 = (0); return (h$newByteArray(8)); };
}
/** @const */ var h$base_default_buffer_size = 32768;
function h$base_c_s_issock(mode) {
    return 0; // fixme
}
/** @const */ var h$base_SEEK_SET = 0;
/** @const */ var h$base_SEEK_CUR = 1;
/** @const */ var h$base_SEEK_END = 2;
function h$base_set_saved_termios(a, b, c) {
    { h$ret1 = (0); return (null); };
}
function h$base_get_saved_termios(r) {
    { h$ret1 = (0); return (null); };
}
// fixme
function h$lockFile(fd, dev, ino, for_writing) {
    ;
    return 0;
}
function h$unlockFile(fd) {
    ;
    return 0;
}
// engine-dependent setup
var h$base_readStdin , h$base_writeStderr, h$base_writeStdout;
var h$base_closeStdin = null, h$base_closeStderr = null, h$base_closeStdout = null;
var h$base_readFile, h$base_writeFile, h$base_closeFile;
var h$base_stdin_waiting = new h$Queue();
var h$base_stdin_chunk = { buf: null
                           , pos: 0
                           , processing: false
                           };
var h$base_stdin_eof = false;
var h$base_process_stdin = function() {
    var c = h$base_stdin_chunk;
    var q = h$base_stdin_waiting;
    if(!q.length() || c.processing) return;
    c.processing = true;
    if(!c.buf) { c.pos = 0; c.buf = process.stdin.read(); }
    while(c.buf && q.length()) {
        var x = q.dequeue();
        var n = Math.min(c.buf.length - c.pos, x.n);
        for(var i=0;i<n;i++) {
            x.buf.u8[i+x.off] = c.buf[c.pos+i];
        }
        c.pos += n;
        x.c(n);
        if(c.pos >= c.buf.length) c.buf = null;
        if(!c.buf && q.length()) { c.pos = 0; c.buf = process.stdin.read(); }
    }
    while(h$base_stdin_eof && q.length()) q.dequeue().c(0);
    c.processing = false;
}
if(h$isNode) {
    h$base_closeFile = function(fd, fdo, c) {
        h$fs.close(fd, function(err) {
            delete h$base_fds[fd];
            h$handleErrnoC(err, -1, 0, c);
        });
    }
    h$base_readFile = function(fd, fdo, buf, buf_offset, n, c) {
        var pos = typeof fdo.pos === 'number' ? fdo.pos : null;
        ;
        h$fs.read(fd, new Buffer(n), 0, n, pos, function(err, bytesRead, nbuf) {
            if(err) {
                h$setErrno(err);
                c(-1);
            } else {
                for(var i=bytesRead-1;i>=0;i--) buf.u8[buf_offset+i] = nbuf[i];
                if(typeof fdo.pos === 'number') fdo.pos += bytesRead;
                c(bytesRead);
            }
        });
    }
    h$base_readStdin = function(fd, fdo, buf, buf_offset, n, c) {
        ;
        h$base_stdin_waiting.enqueue({buf: buf, off: buf_offset, n: n, c: c});
        h$base_process_stdin();
    }
    h$base_closeStdin = function(fd, fdo, c) {
        ;
        // process.stdin.close(); fixme
        c(0);
    }
    h$base_writeFile = function(fd, fdo, buf, buf_offset, n, c) {
        var pos = typeof fdo.pos === 'number' ? fdo.pos : null;
        ;
        var nbuf = new Buffer(n);
        for(var i=0;i<n;i++) nbuf[i] = buf.u8[i+buf_offset];
        if(typeof fdo.pos === 'number') fdo.pos += n;
        h$fs.write(fd, nbuf, 0, n, pos, function(err, bytesWritten) {
            ;
            if(err) {
                h$setErrno(err);
                if(typeof fdo.pos === 'number') fdo.pos -= n;
                if(h$errno === 35)
                    setTimeout(function() { h$base_writeFile(fd, fdo, buf, buf_offset, n, c); }, 20);
                else c(-1);
            } else {
                if(typeof fdo.pos === 'number') fdo.pos += bytesWritten - n;
                c(bytesWritten);
            }
        });
    }
    h$base_writeStdout = function(fd, fdo, buf, buf_offset, n, c) {
        ;
        h$base_writeFile(1, fdo, buf, buf_offset, n, c);
    }
    h$base_closeStdout = function(fd, fdo, c) {
        ;
 // not actually closed, fixme?
        c(0);
    }
    h$base_writeStderr = function(fd, fdo, buf, buf_offset, n, c) {
        ;
        h$base_writeFile(2, fdo, buf, buf_offset, n, c);
    }
    h$base_closeStderr = function(fd, fdo, c) {
        ;
 // not actually closed, fixme?
        c(0);
    }
    process.stdin.on('readable', h$base_process_stdin);
    process.stdin.on('end', function() { h$base_stdin_eof = true; h$base_process_stdin(); });
} else if (h$isJsShell) {
    h$base_readStdin = function(fd, fdo, buf, buf_offset, n, c) {
        c(0);
    }
    h$base_writeStdout = function(fd, fdo, buf, buf_offset, n, c) {
        putstr(h$decodeUtf8(buf, n, buf_offset));
        c(n);
    }
    h$base_writeStderr = function(fd, fdo, buf, buf_offset, n, c) {
        printErr(h$decodeUtf8(buf, n, buf_offset));
        c(n);
    }
} else if(h$isJsCore) {
    h$base_readStdin = function(fd, fdo, buf, buf_offset, n, c) {
 c(0);
    }
    var h$base_stdoutLeftover = { f: print, val: null };
    var h$base_stderrLeftover = { f: debug, val: null };
    var h$base_writeWithLeftover = function(buf, n, buf_offset, c, lo) {
 var lines = h$decodeUtf8(buf, n, buf_offset).split(/\r?\n/);
 if(lines.length === 1) {
     if(lines[0].length) {
  if(lo.val !== null) lo.val += lines[0];
  else lo.val = lines[0];
     }
 } else {
            lo.f(((lo.val !== null) ? lo.val : '') + lines[0]);
     for(var i=1;i<lines.length-1;i++) lo.f(lines[i]);
     if(lines[lines.length-1].length) lo.val = lines[lines.length-1];
     else lo.val = null;
 }
 c(n);
    }
    h$base_writeStdout = function(fd, fdo, buf, buf_offset, n, c) {
 h$base_writeWithLeftover(buf, n, buf_offset, c, h$base_stdoutLeftover);
    }
    h$base_writeStderr = function(fd, fdo, buf, buf_offset, n, c) {
 // writing to stderr not supported, write to stdout
 h$base_writeWithLeftover(buf, n, buf_offset, c, h$base_stderrLeftover);
    }
} else { // browser / fallback
    h$base_readStdin = function(fd, fdo, buf, buf_offset, n, c) {
        c(0);
    }
    h$base_writeStdout = function(fd, fdo, buf, buf_offset, n, c) {
        console.log(h$decodeUtf8(buf, n, buf_offset));
        c(n);
    }
    h$base_writeStderr = function(fd, fdo, buf, buf_offset, n, c) {
        console.log(h$decodeUtf8(buf, n, buf_offset));
        c(n);
    }
}
var h$base_stdin_fd = { read: h$base_readStdin, close: h$base_closeStdin };
var h$base_stdout_fd = { write: h$base_writeStdout, close: h$base_closeStdout };
var h$base_stderr_fd = { write: h$base_writeStderr, close: h$base_closeStderr };
var h$base_fdN = -1; // negative file descriptors are 'virtual'
var h$base_fds = [h$base_stdin_fd, h$base_stdout_fd, h$base_stderr_fd];
function h$shutdownHaskellAndExit(code, fast) {
    h$exitProcess(code);
}
// RAND_MAX = 32767
function h$rand() {
  return (32768 * Math.random()) & 32767;
}
/* Copyright (C) 1991-2017 Free Software Foundation, Inc.
   This file is part of the GNU C Library.

   The GNU C Library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2.1 of the License, or (at your option) any later version.

   The GNU C Library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public
   License along with the GNU C Library; if not, see
   <http://www.gnu.org/licenses/>.  */
/* This header is separate from features.h so that the compiler can
   include it implicitly at the start of every compilation.  It must
   not itself include <features.h> or any other header that includes
   <features.h> because the implicit include comes before any feature
   test macros that may be defined in a source file before it first
   explicitly includes a system header.  GCC knows the name of this
   header in order to preinclude it.  */
/* glibc's intent is to support the IEC 559 math functionality, real
   and complex.  If the GCC (4.9 and later) predefined macros
   specifying compiler intent are available, use them to determine
   whether the overall intent is to support these features; otherwise,
   presume an older compiler has intent to support these features and
   define these macros by default.  */
/* wchar_t uses Unicode 8.0.0.  Version 8.0 of the Unicode Standard is
   synchronized with ISO/IEC 10646:2014, plus Amendment 1 (published
   2015-05-15).  */
/* We do not support C11 <threads.h>.  */
function h$hsprimitive_memcpy(dst_d, dst_o, doff, src_d, src_o, soff, len) {
  return h$primitive_memmove(dst_d, dst_o, doff, src_d, src_o, len);
}
function h$hsprimitive_memmove(dst_d, dst_o, doff, src_d, src_o, soff, len) {
  if(len === 0) return;
  var du8 = dst_d.u8, su8 = src_d.u8;
  for(var i=len-1;i>=0;i--) {
    du8[dst_o+i] = su8[src_o+i];
  }
}
function h$hsprimitive_memsetba_Word8 (p_d, off, n, x) { if(n > 0) { if(p_d.u8.fill) p_d.u8.fill(x, off, off + n); else for(var i=off; i<off+n; i++) p_d.u8[i] = x; } }
function h$hsprimitive_memsetba_Word16 (p_d, off, n, x) { if(n > 0) { if(p_d.u1.fill) p_d.u1.fill(x, off, off + n); else for(var i=off; i<off+n; i++) p_d.u1[i] = x; } }
function h$hsprimitive_memsetba_Word32 (p_d, off, n, x) { if(n > 0) { if(p_d.i3.fill) p_d.i3.fill(x, off, off + n); else for(var i=off; i<off+n; i++) p_d.i3[i] = x; } }
function h$hsprimitive_memsetba_Word (p_d, off, n, x) { if(n > 0) { if(p_d.i3.fill) p_d.i3.fill(x, off, off + n); else for(var i=off; i<off+n; i++) p_d.i3[i] = x; } }
function h$hsprimitive_memsetba_Float (p_d, off, n, x) { if(n > 0) { if(p_d.f3.fill) p_d.f3.fill(x, off, off + n); else for(var i=off; i<off+n; i++) p_d.f3[i] = x; } }
function h$hsprimitive_memsetba_Double (p_d, off, n, x) { if(n > 0) { if(p_d.f6.fill) p_d.f6.fill(x, off, off + n); else for(var i=off; i<off+n; i++) p_d.f6[i] = x; } }
function h$hsprimitive_memsetba_Char (p_d, off, n, x) { if(n > 0) { if(p_d.i3.fill) p_d.i3.fill(x, off, off + n); else for(var i=off; i<off+n; i++) p_d.i3[i] = x; } }
function h$hsprimitive_memset_Word8 (p_d, p_o, off, n, x) { var start = (p_o >> 0) + off; if(n > 0) { if(p_d.u8.fill) p_d.u8.fill(x, start, start + n); else for(var i=start; i<start+n; i++) p_d.u8[i] = x; } }
function h$hsprimitive_memset_Word16 (p_d, p_o, off, n, x) { var start = (p_o >> 1) + off; if(n > 0) { if(p_d.u1.fill) p_d.u1.fill(x, start, start + n); else for(var i=start; i<start+n; i++) p_d.u1[i] = x; } }
function h$hsprimitive_memset_Word32 (p_d, p_o, off, n, x) { var start = (p_o >> 2) + off; if(n > 0) { if(p_d.i3.fill) p_d.i3.fill(x, start, start + n); else for(var i=start; i<start+n; i++) p_d.i3[i] = x; } }
function h$hsprimitive_memset_Word (p_d, p_o, off, n, x) { var start = (p_o >> 2) + off; if(n > 0) { if(p_d.i3.fill) p_d.i3.fill(x, start, start + n); else for(var i=start; i<start+n; i++) p_d.i3[i] = x; } }
function h$hsprimitive_memset_Float (p_d, p_o, off, n, x) { var start = (p_o >> 2) + off; if(n > 0) { if(p_d.f3.fill) p_d.f3.fill(x, start, start + n); else for(var i=start; i<start+n; i++) p_d.f3[i] = x; } }
function h$hsprimitive_memset_Double (p_d, p_o, off, n, x) { var start = (p_o >> 3) + off; if(n > 0) { if(p_d.f6.fill) p_d.f6.fill(x, start, start + n); else for(var i=start; i<start+n; i++) p_d.f6[i] = x; } }
function h$hsprimitive_memset_Char (p_d, p_o, off, n, x) { var start = (p_o >> 2) + off; if(n > 0) { if(p_d.i3.fill) p_d.i3.fill(x, start, start + n); else for(var i=start; i<start+n; i++) p_d.i3[i] = x; } }
function h$hsprimitive_memsetba_Word64(p_d, off, n, x_1, x_2) {
  h$hsprimitive_memset_Word64(p_d, 0, off, n, x_1, x_2);
}
function h$hsprimitive_memset_Word64(p_d, p_o, off, n, x_1, x_2) {
  var start = (p_o >> 3) + off;
  if(n > 0) {
    var pi3 = p_d.i3;
    for(var i = 0; i < n; i++) {
      var o = (start + i) << 1;
      pi3[o] = x_1;
      pi3[o+1] = x_2;
    }
  }
}
function h$hsprimitive_memset_Ptr(p_d, p_o, off, n, x_1, x_2) {
  if(n > 0) {
    if(!p_d.arr) p_d.arr = [];
    var a = p_d.arr;
    for(var i = 0; i < n; i++) {
      a[p_o + ((off + i) << 2)] = [x_1, x_2];
    }
  }
}
/* Copyright (C) 1991-2017 Free Software Foundation, Inc.
   This file is part of the GNU C Library.

   The GNU C Library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2.1 of the License, or (at your option) any later version.

   The GNU C Library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public
   License along with the GNU C Library; if not, see
   <http://www.gnu.org/licenses/>.  */
/* This header is separate from features.h so that the compiler can
   include it implicitly at the start of every compilation.  It must
   not itself include <features.h> or any other header that includes
   <features.h> because the implicit include comes before any feature
   test macros that may be defined in a source file before it first
   explicitly includes a system header.  GCC knows the name of this
   header in order to preinclude it.  */
/* glibc's intent is to support the IEC 559 math functionality, real
   and complex.  If the GCC (4.9 and later) predefined macros
   specifying compiler intent are available, use them to determine
   whether the overall intent is to support these features; otherwise,
   presume an older compiler has intent to support these features and
   define these macros by default.  */
/* wchar_t uses Unicode 8.0.0.  Version 8.0 of the Unicode Standard is
   synchronized with ISO/IEC 10646:2014, plus Amendment 1 (published
   2015-05-15).  */
/* We do not support C11 <threads.h>.  */
function h$get_current_timezone_seconds(t, pdst_v, pdst_o, pname_v, pname_o) {
    var d = new Date(t * 1000);
    var now = new Date();
    var jan = new Date(now.getFullYear(),0,1);
    var jul = new Date(now.getFullYear(),6,1);
    var stdOff = Math.max(jan.getTimezoneOffset(), jul.getTimezoneOffset());
    var isDst = d.getTimezoneOffset() < stdOff;
    var tzo = d.getTimezoneOffset();
    pdst_v.dv.setInt32(pdst_o, isDst ? 1 : 0, true);
    if(!pname_v.arr) pname_v.arr = [];
    var offstr = tzo < 0 ? ('+' + (tzo/-60)) : ('' + (tzo/-60));
    pname_v.arr[pname_o] = [h$encodeUtf8("UTC" + offstr), 0];
    return (-60*tzo)|0;
}
function h$clock_gettime(when, p_d, p_o) {
/*  h$log("clock_gettime");
  h$log(when);
  h$log(p_d);
  h$log(p_o); */
  var o = p_o >> 2,
      t = Date.now ? Date.now() : new Date().getTime(),
      tf = Math.floor(t / 1000),
      tn = 1000000 * (t - (1000 * tf));
  p_d.i3[o] = tf|0;
  p_d.i3[o+1] = tn|0;
  return 0;
}
/* Copyright (C) 1991-2017 Free Software Foundation, Inc.
   This file is part of the GNU C Library.

   The GNU C Library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2.1 of the License, or (at your option) any later version.

   The GNU C Library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public
   License along with the GNU C Library; if not, see
   <http://www.gnu.org/licenses/>.  */
/* This header is separate from features.h so that the compiler can
   include it implicitly at the start of every compilation.  It must
   not itself include <features.h> or any other header that includes
   <features.h> because the implicit include comes before any feature
   test macros that may be defined in a source file before it first
   explicitly includes a system header.  GCC knows the name of this
   header in order to preinclude it.  */
/* glibc's intent is to support the IEC 559 math functionality, real
   and complex.  If the GCC (4.9 and later) predefined macros
   specifying compiler intent are available, use them to determine
   whether the overall intent is to support these features; otherwise,
   presume an older compiler has intent to support these features and
   define these macros by default.  */
/* wchar_t uses Unicode 8.0.0.  Version 8.0 of the Unicode Standard is
   synchronized with ISO/IEC 10646:2014, plus Amendment 1 (published
   2015-05-15).  */
/* We do not support C11 <threads.h>.  */
// generated by generate_threefish_block.hs
var h$Threefish_256_Process_Block;
h$Threefish_256_Process_Block=function(p,q,y,r){var m;m=p.i3;var a;a=q.i3;y=y.i3;var b,g,l,c,d,h,k,e,f,t,u,v,n,w,x;q=m[0];p=m[1];r=m[2];t=m[3];u=m[4];v=m[5];n=m[6];m=m[7];w=q^r^u^n^2851871266;x=p^t^v^m^466688986;b=a[0];g=a[1];c=a[2];d=a[3];h=a[4];k=a[5];e=a[6];f=a[7];a=(b&16777215)+(q&16777215);b=(a>>>24)+(b>>>24)+(q>>>24)+((g&65535)<<8)+((p&65535)<<8);l=((b>>>24)+(g>>>16)+(p>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=(c&16777215)+(r&16777215)+0;b=(a>>>24)+(c>>>24)+(r>>>24)+0+((d&65535)<<8)+((t&
65535)<<8)+0;d=((b>>>24)+(d>>>16)+(t>>>16)+0<<16)+(b>>8&65535);c=b<<24|a&16777215;a=(h&16777215)+(u&16777215)+0;b=(a>>>24)+(h>>>24)+(u>>>24)+0+((k&65535)<<8)+((v&65535)<<8)+0;k=((b>>>24)+(k>>>16)+(v>>>16)+0<<16)+(b>>8&65535);h=b<<24|a&16777215;a=(e&16777215)+(n&16777215);b=(a>>>24)+(e>>>24)+(n>>>24)+((f&65535)<<8)+((m&65535)<<8);f=((b>>>24)+(f>>>16)+(m>>>16)<<16)+(b>>8&65535);e=b<<24|a&16777215;a=(g&16777215)+(c&16777215);b=(a>>>24)+(g>>>24)+(c>>>24)+((l&65535)<<8)+((d&65535)<<8);l=((b>>>24)+(l>>>
16)+(d>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=d;d=(d<<14|c>>>18)^l;c=(c<<14|a>>>18)^g;a=(h&16777215)+(e&16777215);b=(a>>>24)+(h>>>24)+(e>>>24)+((k&65535)<<8)+((f&65535)<<8);k=((b>>>24)+(k>>>16)+(f>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=f;f=(f<<16|e>>>16)^k;e=(e<<16|a>>>16)^h;a=(g&16777215)+(e&16777215);b=(a>>>24)+(g>>>24)+(e>>>24)+((l&65535)<<8)+((f&65535)<<8);l=((b>>>24)+(l>>>16)+(f>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=f;f=(e<<20|f>>>12)^l;e=(a<<20|e>>>12)^g;a=(h&16777215)+(c&
16777215);b=(a>>>24)+(h>>>24)+(c>>>24)+((k&65535)<<8)+((d&65535)<<8);k=((b>>>24)+(k>>>16)+(d>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=d;d=(c<<25|d>>>7)^k;c=(a<<25|c>>>7)^h;a=(g&16777215)+(c&16777215);b=(a>>>24)+(g>>>24)+(c>>>24)+((l&65535)<<8)+((d&65535)<<8);l=((b>>>24)+(l>>>16)+(d>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=d;d=(d<<23|c>>>9)^l;c=(c<<23|a>>>9)^g;a=(h&16777215)+(e&16777215);b=(a>>>24)+(h>>>24)+(e>>>24)+((k&65535)<<8)+((f&65535)<<8);k=((b>>>24)+(k>>>16)+(f>>>16)<<16)+(b>>8&65535);
h=b<<24|a&16777215;a=f;f=(e<<8|f>>>24)^k;e=(a<<8|e>>>24)^h;a=(g&16777215)+(e&16777215);b=(a>>>24)+(g>>>24)+(e>>>24)+((l&65535)<<8)+((f&65535)<<8);l=((b>>>24)+(l>>>16)+(f>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=f;f=(f<<5|e>>>27)^l;e=(e<<5|a>>>27)^g;a=(h&16777215)+(c&16777215);b=(a>>>24)+(h>>>24)+(c>>>24)+((k&65535)<<8)+((d&65535)<<8);k=((b>>>24)+(k>>>16)+(d>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=d;d=(c<<5|d>>>27)^k;c=(a<<5|c>>>27)^h;a=(g&16777215)+(r&16777215);b=(a>>>24)+(g>>>24)+(r>>>24)+
((l&65535)<<8)+((t&65535)<<8);l=((b>>>24)+(l>>>16)+(t>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=(c&16777215)+(u&16777215)+0;b=(a>>>24)+(c>>>24)+(u>>>24)+0+((d&65535)<<8)+((v&65535)<<8)+0;d=((b>>>24)+(d>>>16)+(v>>>16)+0<<16)+(b>>8&65535);c=b<<24|a&16777215;a=(h&16777215)+(n&16777215)+0;b=(a>>>24)+(h>>>24)+(n>>>24)+0+((k&65535)<<8)+((m&65535)<<8)+0;k=((b>>>24)+(k>>>16)+(m>>>16)+0<<16)+(b>>8&65535);h=b<<24|a&16777215;a=(e&16777215)+(w&16777215)+1;b=(a>>>24)+(e>>>24)+(w>>>24)+0+((f&65535)<<8)+((x&
65535)<<8)+0;f=((b>>>24)+(f>>>16)+(x>>>16)+0<<16)+(b>>8&65535);e=b<<24|a&16777215;a=(g&16777215)+(c&16777215);b=(a>>>24)+(g>>>24)+(c>>>24)+((l&65535)<<8)+((d&65535)<<8);l=((b>>>24)+(l>>>16)+(d>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=d;d=(d<<25|c>>>7)^l;c=(c<<25|a>>>7)^g;a=(h&16777215)+(e&16777215);b=(a>>>24)+(h>>>24)+(e>>>24)+((k&65535)<<8)+((f&65535)<<8);k=((b>>>24)+(k>>>16)+(f>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=f;f=(e<<1|f>>>31)^k;e=(a<<1|e>>>31)^h;a=(g&16777215)+(e&16777215);b=(a>>>
24)+(g>>>24)+(e>>>24)+((l&65535)<<8)+((f&65535)<<8);l=((b>>>24)+(l>>>16)+(f>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=f;f=(e<<14|f>>>18)^l;e=(a<<14|e>>>18)^g;a=(h&16777215)+(c&16777215);b=(a>>>24)+(h>>>24)+(c>>>24)+((k&65535)<<8)+((d&65535)<<8);k=((b>>>24)+(k>>>16)+(d>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=d;d=(d<<12|c>>>20)^k;c=(c<<12|a>>>20)^h;a=(g&16777215)+(c&16777215);b=(a>>>24)+(g>>>24)+(c>>>24)+((l&65535)<<8)+((d&65535)<<8);l=((b>>>24)+(l>>>16)+(d>>>16)<<16)+(b>>8&65535);g=b<<24|a&
16777215;a=d;d=(c<<26|d>>>6)^l;c=(a<<26|c>>>6)^g;a=(h&16777215)+(e&16777215);b=(a>>>24)+(h>>>24)+(e>>>24)+((k&65535)<<8)+((f&65535)<<8);k=((b>>>24)+(k>>>16)+(f>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=f;f=(f<<22|e>>>10)^k;e=(e<<22|a>>>10)^h;a=(g&16777215)+(e&16777215);b=(a>>>24)+(g>>>24)+(e>>>24)+((l&65535)<<8)+((f&65535)<<8);l=((b>>>24)+(l>>>16)+(f>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=f;f=e^l;e=a^g;a=(h&16777215)+(c&16777215);b=(a>>>24)+(h>>>24)+(c>>>24)+((k&65535)<<8)+((d&65535)<<8);
k=((b>>>24)+(k>>>16)+(d>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=d;d=c^k;c=a^h;a=(g&16777215)+(u&16777215);b=(a>>>24)+(g>>>24)+(u>>>24)+((l&65535)<<8)+((v&65535)<<8);l=((b>>>24)+(l>>>16)+(v>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=(c&16777215)+(n&16777215)+0;b=(a>>>24)+(c>>>24)+(n>>>24)+0+((d&65535)<<8)+((m&65535)<<8)+0;d=((b>>>24)+(d>>>16)+(m>>>16)+0<<16)+(b>>8&65535);c=b<<24|a&16777215;a=(h&16777215)+(w&16777215)+0;b=(a>>>24)+(h>>>24)+(w>>>24)+0+((k&65535)<<8)+((x&65535)<<8)+0;k=((b>>>24)+
(k>>>16)+(x>>>16)+0<<16)+(b>>8&65535);h=b<<24|a&16777215;a=(e&16777215)+(q&16777215)+2;b=(a>>>24)+(e>>>24)+(q>>>24)+0+((f&65535)<<8)+((p&65535)<<8)+0;f=((b>>>24)+(f>>>16)+(p>>>16)+0<<16)+(b>>8&65535);e=b<<24|a&16777215;a=(g&16777215)+(c&16777215);b=(a>>>24)+(g>>>24)+(c>>>24)+((l&65535)<<8)+((d&65535)<<8);l=((b>>>24)+(l>>>16)+(d>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=d;d=(d<<14|c>>>18)^l;c=(c<<14|a>>>18)^g;a=(h&16777215)+(e&16777215);b=(a>>>24)+(h>>>24)+(e>>>24)+((k&65535)<<8)+((f&65535)<<8);
k=((b>>>24)+(k>>>16)+(f>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=f;f=(f<<16|e>>>16)^k;e=(e<<16|a>>>16)^h;a=(g&16777215)+(e&16777215);b=(a>>>24)+(g>>>24)+(e>>>24)+((l&65535)<<8)+((f&65535)<<8);l=((b>>>24)+(l>>>16)+(f>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=f;f=(e<<20|f>>>12)^l;e=(a<<20|e>>>12)^g;a=(h&16777215)+(c&16777215);b=(a>>>24)+(h>>>24)+(c>>>24)+((k&65535)<<8)+((d&65535)<<8);k=((b>>>24)+(k>>>16)+(d>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=d;d=(c<<25|d>>>7)^k;c=(a<<25|c>>>7)^h;a=
(g&16777215)+(c&16777215);b=(a>>>24)+(g>>>24)+(c>>>24)+((l&65535)<<8)+((d&65535)<<8);l=((b>>>24)+(l>>>16)+(d>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=d;d=(d<<23|c>>>9)^l;c=(c<<23|a>>>9)^g;a=(h&16777215)+(e&16777215);b=(a>>>24)+(h>>>24)+(e>>>24)+((k&65535)<<8)+((f&65535)<<8);k=((b>>>24)+(k>>>16)+(f>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=f;f=(e<<8|f>>>24)^k;e=(a<<8|e>>>24)^h;a=(g&16777215)+(e&16777215);b=(a>>>24)+(g>>>24)+(e>>>24)+((l&65535)<<8)+((f&65535)<<8);l=((b>>>24)+(l>>>16)+(f>>>16)<<
16)+(b>>8&65535);g=b<<24|a&16777215;a=f;f=(f<<5|e>>>27)^l;e=(e<<5|a>>>27)^g;a=(h&16777215)+(c&16777215);b=(a>>>24)+(h>>>24)+(c>>>24)+((k&65535)<<8)+((d&65535)<<8);k=((b>>>24)+(k>>>16)+(d>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=d;d=(c<<5|d>>>27)^k;c=(a<<5|c>>>27)^h;a=(g&16777215)+(n&16777215);b=(a>>>24)+(g>>>24)+(n>>>24)+((l&65535)<<8)+((m&65535)<<8);l=((b>>>24)+(l>>>16)+(m>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=(c&16777215)+(w&16777215)+0;b=(a>>>24)+(c>>>24)+(w>>>24)+0+((d&65535)<<8)+((x&
65535)<<8)+0;d=((b>>>24)+(d>>>16)+(x>>>16)+0<<16)+(b>>8&65535);c=b<<24|a&16777215;a=(h&16777215)+(q&16777215)+0;b=(a>>>24)+(h>>>24)+(q>>>24)+0+((k&65535)<<8)+((p&65535)<<8)+0;k=((b>>>24)+(k>>>16)+(p>>>16)+0<<16)+(b>>8&65535);h=b<<24|a&16777215;a=(e&16777215)+(r&16777215)+3;b=(a>>>24)+(e>>>24)+(r>>>24)+0+((f&65535)<<8)+((t&65535)<<8)+0;f=((b>>>24)+(f>>>16)+(t>>>16)+0<<16)+(b>>8&65535);e=b<<24|a&16777215;a=(g&16777215)+(c&16777215);b=(a>>>24)+(g>>>24)+(c>>>24)+((l&65535)<<8)+((d&65535)<<8);l=((b>>>
24)+(l>>>16)+(d>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=d;d=(d<<25|c>>>7)^l;c=(c<<25|a>>>7)^g;a=(h&16777215)+(e&16777215);b=(a>>>24)+(h>>>24)+(e>>>24)+((k&65535)<<8)+((f&65535)<<8);k=((b>>>24)+(k>>>16)+(f>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=f;f=(e<<1|f>>>31)^k;e=(a<<1|e>>>31)^h;a=(g&16777215)+(e&16777215);b=(a>>>24)+(g>>>24)+(e>>>24)+((l&65535)<<8)+((f&65535)<<8);l=((b>>>24)+(l>>>16)+(f>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=f;f=(e<<14|f>>>18)^l;e=(a<<14|e>>>18)^g;a=(h&16777215)+
(c&16777215);b=(a>>>24)+(h>>>24)+(c>>>24)+((k&65535)<<8)+((d&65535)<<8);k=((b>>>24)+(k>>>16)+(d>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=d;d=(d<<12|c>>>20)^k;c=(c<<12|a>>>20)^h;a=(g&16777215)+(c&16777215);b=(a>>>24)+(g>>>24)+(c>>>24)+((l&65535)<<8)+((d&65535)<<8);l=((b>>>24)+(l>>>16)+(d>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=d;d=(c<<26|d>>>6)^l;c=(a<<26|c>>>6)^g;a=(h&16777215)+(e&16777215);b=(a>>>24)+(h>>>24)+(e>>>24)+((k&65535)<<8)+((f&65535)<<8);k=((b>>>24)+(k>>>16)+(f>>>16)<<16)+(b>>
8&65535);h=b<<24|a&16777215;a=f;f=(f<<22|e>>>10)^k;e=(e<<22|a>>>10)^h;a=(g&16777215)+(e&16777215);b=(a>>>24)+(g>>>24)+(e>>>24)+((l&65535)<<8)+((f&65535)<<8);l=((b>>>24)+(l>>>16)+(f>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=f;f=e^l;e=a^g;a=(h&16777215)+(c&16777215);b=(a>>>24)+(h>>>24)+(c>>>24)+((k&65535)<<8)+((d&65535)<<8);k=((b>>>24)+(k>>>16)+(d>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=d;d=c^k;c=a^h;a=(g&16777215)+(w&16777215);b=(a>>>24)+(g>>>24)+(w>>>24)+((l&65535)<<8)+((x&65535)<<8);l=((b>>>
24)+(l>>>16)+(x>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=(c&16777215)+(q&16777215)+0;b=(a>>>24)+(c>>>24)+(q>>>24)+0+((d&65535)<<8)+((p&65535)<<8)+0;d=((b>>>24)+(d>>>16)+(p>>>16)+0<<16)+(b>>8&65535);c=b<<24|a&16777215;a=(h&16777215)+(r&16777215)+0;b=(a>>>24)+(h>>>24)+(r>>>24)+0+((k&65535)<<8)+((t&65535)<<8)+0;k=((b>>>24)+(k>>>16)+(t>>>16)+0<<16)+(b>>8&65535);h=b<<24|a&16777215;a=(e&16777215)+(u&16777215)+4;b=(a>>>24)+(e>>>24)+(u>>>24)+0+((f&65535)<<8)+((v&65535)<<8)+0;f=((b>>>24)+(f>>>16)+(v>>>
16)+0<<16)+(b>>8&65535);e=b<<24|a&16777215;a=(g&16777215)+(c&16777215);b=(a>>>24)+(g>>>24)+(c>>>24)+((l&65535)<<8)+((d&65535)<<8);l=((b>>>24)+(l>>>16)+(d>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=d;d=(d<<14|c>>>18)^l;c=(c<<14|a>>>18)^g;a=(h&16777215)+(e&16777215);b=(a>>>24)+(h>>>24)+(e>>>24)+((k&65535)<<8)+((f&65535)<<8);k=((b>>>24)+(k>>>16)+(f>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=f;f=(f<<16|e>>>16)^k;e=(e<<16|a>>>16)^h;a=(g&16777215)+(e&16777215);b=(a>>>24)+(g>>>24)+(e>>>24)+((l&65535)<<
8)+((f&65535)<<8);l=((b>>>24)+(l>>>16)+(f>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=f;f=(e<<20|f>>>12)^l;e=(a<<20|e>>>12)^g;a=(h&16777215)+(c&16777215);b=(a>>>24)+(h>>>24)+(c>>>24)+((k&65535)<<8)+((d&65535)<<8);k=((b>>>24)+(k>>>16)+(d>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=d;d=(c<<25|d>>>7)^k;c=(a<<25|c>>>7)^h;a=(g&16777215)+(c&16777215);b=(a>>>24)+(g>>>24)+(c>>>24)+((l&65535)<<8)+((d&65535)<<8);l=((b>>>24)+(l>>>16)+(d>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=d;d=(d<<23|c>>>9)^l;c=(c<<
23|a>>>9)^g;a=(h&16777215)+(e&16777215);b=(a>>>24)+(h>>>24)+(e>>>24)+((k&65535)<<8)+((f&65535)<<8);k=((b>>>24)+(k>>>16)+(f>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=f;f=(e<<8|f>>>24)^k;e=(a<<8|e>>>24)^h;a=(g&16777215)+(e&16777215);b=(a>>>24)+(g>>>24)+(e>>>24)+((l&65535)<<8)+((f&65535)<<8);l=((b>>>24)+(l>>>16)+(f>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=f;f=(f<<5|e>>>27)^l;e=(e<<5|a>>>27)^g;a=(h&16777215)+(c&16777215);b=(a>>>24)+(h>>>24)+(c>>>24)+((k&65535)<<8)+((d&65535)<<8);k=((b>>>24)+(k>>>
16)+(d>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=d;d=(c<<5|d>>>27)^k;c=(a<<5|c>>>27)^h;a=(g&16777215)+(q&16777215);b=(a>>>24)+(g>>>24)+(q>>>24)+((l&65535)<<8)+((p&65535)<<8);l=((b>>>24)+(l>>>16)+(p>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=(c&16777215)+(r&16777215)+0;b=(a>>>24)+(c>>>24)+(r>>>24)+0+((d&65535)<<8)+((t&65535)<<8)+0;d=((b>>>24)+(d>>>16)+(t>>>16)+0<<16)+(b>>8&65535);c=b<<24|a&16777215;a=(h&16777215)+(u&16777215)+0;b=(a>>>24)+(h>>>24)+(u>>>24)+0+((k&65535)<<8)+((v&65535)<<8)+0;k=
((b>>>24)+(k>>>16)+(v>>>16)+0<<16)+(b>>8&65535);h=b<<24|a&16777215;a=(e&16777215)+(n&16777215)+5;b=(a>>>24)+(e>>>24)+(n>>>24)+0+((f&65535)<<8)+((m&65535)<<8)+0;f=((b>>>24)+(f>>>16)+(m>>>16)+0<<16)+(b>>8&65535);e=b<<24|a&16777215;a=(g&16777215)+(c&16777215);b=(a>>>24)+(g>>>24)+(c>>>24)+((l&65535)<<8)+((d&65535)<<8);l=((b>>>24)+(l>>>16)+(d>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=d;d=(d<<25|c>>>7)^l;c=(c<<25|a>>>7)^g;a=(h&16777215)+(e&16777215);b=(a>>>24)+(h>>>24)+(e>>>24)+((k&65535)<<8)+((f&65535)<<
8);k=((b>>>24)+(k>>>16)+(f>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=f;f=(e<<1|f>>>31)^k;e=(a<<1|e>>>31)^h;a=(g&16777215)+(e&16777215);b=(a>>>24)+(g>>>24)+(e>>>24)+((l&65535)<<8)+((f&65535)<<8);l=((b>>>24)+(l>>>16)+(f>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=f;f=(e<<14|f>>>18)^l;e=(a<<14|e>>>18)^g;a=(h&16777215)+(c&16777215);b=(a>>>24)+(h>>>24)+(c>>>24)+((k&65535)<<8)+((d&65535)<<8);k=((b>>>24)+(k>>>16)+(d>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=d;d=(d<<12|c>>>20)^k;c=(c<<12|a>>>20)^h;
a=(g&16777215)+(c&16777215);b=(a>>>24)+(g>>>24)+(c>>>24)+((l&65535)<<8)+((d&65535)<<8);l=((b>>>24)+(l>>>16)+(d>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=d;d=(c<<26|d>>>6)^l;c=(a<<26|c>>>6)^g;a=(h&16777215)+(e&16777215);b=(a>>>24)+(h>>>24)+(e>>>24)+((k&65535)<<8)+((f&65535)<<8);k=((b>>>24)+(k>>>16)+(f>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=f;f=(f<<22|e>>>10)^k;e=(e<<22|a>>>10)^h;a=(g&16777215)+(e&16777215);b=(a>>>24)+(g>>>24)+(e>>>24)+((l&65535)<<8)+((f&65535)<<8);l=((b>>>24)+(l>>>16)+(f>>>
16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=f;f=e^l;e=a^g;a=(h&16777215)+(c&16777215);b=(a>>>24)+(h>>>24)+(c>>>24)+((k&65535)<<8)+((d&65535)<<8);k=((b>>>24)+(k>>>16)+(d>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=d;d=c^k;c=a^h;a=(g&16777215)+(r&16777215);b=(a>>>24)+(g>>>24)+(r>>>24)+((l&65535)<<8)+((t&65535)<<8);l=((b>>>24)+(l>>>16)+(t>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=(c&16777215)+(u&16777215)+0;b=(a>>>24)+(c>>>24)+(u>>>24)+0+((d&65535)<<8)+((v&65535)<<8)+0;d=((b>>>24)+(d>>>16)+(v>>>16)+
0<<16)+(b>>8&65535);c=b<<24|a&16777215;a=(h&16777215)+(n&16777215)+0;b=(a>>>24)+(h>>>24)+(n>>>24)+0+((k&65535)<<8)+((m&65535)<<8)+0;k=((b>>>24)+(k>>>16)+(m>>>16)+0<<16)+(b>>8&65535);h=b<<24|a&16777215;a=(e&16777215)+(w&16777215)+6;b=(a>>>24)+(e>>>24)+(w>>>24)+0+((f&65535)<<8)+((x&65535)<<8)+0;f=((b>>>24)+(f>>>16)+(x>>>16)+0<<16)+(b>>8&65535);e=b<<24|a&16777215;a=(g&16777215)+(c&16777215);b=(a>>>24)+(g>>>24)+(c>>>24)+((l&65535)<<8)+((d&65535)<<8);l=((b>>>24)+(l>>>16)+(d>>>16)<<16)+(b>>8&65535);g=b<<
24|a&16777215;a=d;d=(d<<14|c>>>18)^l;c=(c<<14|a>>>18)^g;a=(h&16777215)+(e&16777215);b=(a>>>24)+(h>>>24)+(e>>>24)+((k&65535)<<8)+((f&65535)<<8);k=((b>>>24)+(k>>>16)+(f>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=f;f=(f<<16|e>>>16)^k;e=(e<<16|a>>>16)^h;a=(g&16777215)+(e&16777215);b=(a>>>24)+(g>>>24)+(e>>>24)+((l&65535)<<8)+((f&65535)<<8);l=((b>>>24)+(l>>>16)+(f>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=f;f=(e<<20|f>>>12)^l;e=(a<<20|e>>>12)^g;a=(h&16777215)+(c&16777215);b=(a>>>24)+(h>>>24)+(c>>>
24)+((k&65535)<<8)+((d&65535)<<8);k=((b>>>24)+(k>>>16)+(d>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=d;d=(c<<25|d>>>7)^k;c=(a<<25|c>>>7)^h;a=(g&16777215)+(c&16777215);b=(a>>>24)+(g>>>24)+(c>>>24)+((l&65535)<<8)+((d&65535)<<8);l=((b>>>24)+(l>>>16)+(d>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=d;d=(d<<23|c>>>9)^l;c=(c<<23|a>>>9)^g;a=(h&16777215)+(e&16777215);b=(a>>>24)+(h>>>24)+(e>>>24)+((k&65535)<<8)+((f&65535)<<8);k=((b>>>24)+(k>>>16)+(f>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=f;f=(e<<8|
f>>>24)^k;e=(a<<8|e>>>24)^h;a=(g&16777215)+(e&16777215);b=(a>>>24)+(g>>>24)+(e>>>24)+((l&65535)<<8)+((f&65535)<<8);l=((b>>>24)+(l>>>16)+(f>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=f;f=(f<<5|e>>>27)^l;e=(e<<5|a>>>27)^g;a=(h&16777215)+(c&16777215);b=(a>>>24)+(h>>>24)+(c>>>24)+((k&65535)<<8)+((d&65535)<<8);k=((b>>>24)+(k>>>16)+(d>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=d;d=(c<<5|d>>>27)^k;c=(a<<5|c>>>27)^h;a=(g&16777215)+(u&16777215);b=(a>>>24)+(g>>>24)+(u>>>24)+((l&65535)<<8)+((v&65535)<<8);
l=((b>>>24)+(l>>>16)+(v>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=(c&16777215)+(n&16777215)+0;b=(a>>>24)+(c>>>24)+(n>>>24)+0+((d&65535)<<8)+((m&65535)<<8)+0;d=((b>>>24)+(d>>>16)+(m>>>16)+0<<16)+(b>>8&65535);c=b<<24|a&16777215;a=(h&16777215)+(w&16777215)+0;b=(a>>>24)+(h>>>24)+(w>>>24)+0+((k&65535)<<8)+((x&65535)<<8)+0;k=((b>>>24)+(k>>>16)+(x>>>16)+0<<16)+(b>>8&65535);h=b<<24|a&16777215;a=(e&16777215)+(q&16777215)+7;b=(a>>>24)+(e>>>24)+(q>>>24)+0+((f&65535)<<8)+((p&65535)<<8)+0;f=((b>>>24)+(f>>>
16)+(p>>>16)+0<<16)+(b>>8&65535);e=b<<24|a&16777215;a=(g&16777215)+(c&16777215);b=(a>>>24)+(g>>>24)+(c>>>24)+((l&65535)<<8)+((d&65535)<<8);l=((b>>>24)+(l>>>16)+(d>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=d;d=(d<<25|c>>>7)^l;c=(c<<25|a>>>7)^g;a=(h&16777215)+(e&16777215);b=(a>>>24)+(h>>>24)+(e>>>24)+((k&65535)<<8)+((f&65535)<<8);k=((b>>>24)+(k>>>16)+(f>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=f;f=(e<<1|f>>>31)^k;e=(a<<1|e>>>31)^h;a=(g&16777215)+(e&16777215);b=(a>>>24)+(g>>>24)+(e>>>24)+((l&
65535)<<8)+((f&65535)<<8);l=((b>>>24)+(l>>>16)+(f>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=f;f=(e<<14|f>>>18)^l;e=(a<<14|e>>>18)^g;a=(h&16777215)+(c&16777215);b=(a>>>24)+(h>>>24)+(c>>>24)+((k&65535)<<8)+((d&65535)<<8);k=((b>>>24)+(k>>>16)+(d>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=d;d=(d<<12|c>>>20)^k;c=(c<<12|a>>>20)^h;a=(g&16777215)+(c&16777215);b=(a>>>24)+(g>>>24)+(c>>>24)+((l&65535)<<8)+((d&65535)<<8);l=((b>>>24)+(l>>>16)+(d>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=d;d=(c<<26|d>>>
6)^l;c=(a<<26|c>>>6)^g;a=(h&16777215)+(e&16777215);b=(a>>>24)+(h>>>24)+(e>>>24)+((k&65535)<<8)+((f&65535)<<8);k=((b>>>24)+(k>>>16)+(f>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=f;f=(f<<22|e>>>10)^k;e=(e<<22|a>>>10)^h;a=(g&16777215)+(e&16777215);b=(a>>>24)+(g>>>24)+(e>>>24)+((l&65535)<<8)+((f&65535)<<8);l=((b>>>24)+(l>>>16)+(f>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=f;f=e^l;e=a^g;a=(h&16777215)+(c&16777215);b=(a>>>24)+(h>>>24)+(c>>>24)+((k&65535)<<8)+((d&65535)<<8);k=((b>>>24)+(k>>>16)+(d>>>
16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=d;d=c^k;c=a^h;a=(g&16777215)+(n&16777215);b=(a>>>24)+(g>>>24)+(n>>>24)+((l&65535)<<8)+((m&65535)<<8);l=((b>>>24)+(l>>>16)+(m>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=(c&16777215)+(w&16777215)+0;b=(a>>>24)+(c>>>24)+(w>>>24)+0+((d&65535)<<8)+((x&65535)<<8)+0;d=((b>>>24)+(d>>>16)+(x>>>16)+0<<16)+(b>>8&65535);c=b<<24|a&16777215;a=(h&16777215)+(q&16777215)+0;b=(a>>>24)+(h>>>24)+(q>>>24)+0+((k&65535)<<8)+((p&65535)<<8)+0;k=((b>>>24)+(k>>>16)+(p>>>16)+0<<16)+
(b>>8&65535);h=b<<24|a&16777215;a=(e&16777215)+(r&16777215)+8;b=(a>>>24)+(e>>>24)+(r>>>24)+0+((f&65535)<<8)+((t&65535)<<8)+0;f=((b>>>24)+(f>>>16)+(t>>>16)+0<<16)+(b>>8&65535);e=b<<24|a&16777215;a=(g&16777215)+(c&16777215);b=(a>>>24)+(g>>>24)+(c>>>24)+((l&65535)<<8)+((d&65535)<<8);l=((b>>>24)+(l>>>16)+(d>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=d;d=(d<<14|c>>>18)^l;c=(c<<14|a>>>18)^g;a=(h&16777215)+(e&16777215);b=(a>>>24)+(h>>>24)+(e>>>24)+((k&65535)<<8)+((f&65535)<<8);k=((b>>>24)+(k>>>16)+(f>>>
16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=f;f=(f<<16|e>>>16)^k;e=(e<<16|a>>>16)^h;a=(g&16777215)+(e&16777215);b=(a>>>24)+(g>>>24)+(e>>>24)+((l&65535)<<8)+((f&65535)<<8);l=((b>>>24)+(l>>>16)+(f>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=f;f=(e<<20|f>>>12)^l;e=(a<<20|e>>>12)^g;a=(h&16777215)+(c&16777215);b=(a>>>24)+(h>>>24)+(c>>>24)+((k&65535)<<8)+((d&65535)<<8);k=((b>>>24)+(k>>>16)+(d>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=d;d=(c<<25|d>>>7)^k;c=(a<<25|c>>>7)^h;a=(g&16777215)+(c&16777215);
b=(a>>>24)+(g>>>24)+(c>>>24)+((l&65535)<<8)+((d&65535)<<8);l=((b>>>24)+(l>>>16)+(d>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=d;d=(d<<23|c>>>9)^l;c=(c<<23|a>>>9)^g;a=(h&16777215)+(e&16777215);b=(a>>>24)+(h>>>24)+(e>>>24)+((k&65535)<<8)+((f&65535)<<8);k=((b>>>24)+(k>>>16)+(f>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=f;f=(e<<8|f>>>24)^k;e=(a<<8|e>>>24)^h;a=(g&16777215)+(e&16777215);b=(a>>>24)+(g>>>24)+(e>>>24)+((l&65535)<<8)+((f&65535)<<8);l=((b>>>24)+(l>>>16)+(f>>>16)<<16)+(b>>8&65535);g=b<<24|
a&16777215;a=f;f=(f<<5|e>>>27)^l;e=(e<<5|a>>>27)^g;a=(h&16777215)+(c&16777215);b=(a>>>24)+(h>>>24)+(c>>>24)+((k&65535)<<8)+((d&65535)<<8);k=((b>>>24)+(k>>>16)+(d>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=d;d=(c<<5|d>>>27)^k;c=(a<<5|c>>>27)^h;a=(g&16777215)+(w&16777215);b=(a>>>24)+(g>>>24)+(w>>>24)+((l&65535)<<8)+((x&65535)<<8);l=((b>>>24)+(l>>>16)+(x>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=(c&16777215)+(q&16777215)+0;b=(a>>>24)+(c>>>24)+(q>>>24)+0+((d&65535)<<8)+((p&65535)<<8)+0;d=((b>>>24)+
(d>>>16)+(p>>>16)+0<<16)+(b>>8&65535);c=b<<24|a&16777215;a=(h&16777215)+(r&16777215)+0;b=(a>>>24)+(h>>>24)+(r>>>24)+0+((k&65535)<<8)+((t&65535)<<8)+0;k=((b>>>24)+(k>>>16)+(t>>>16)+0<<16)+(b>>8&65535);h=b<<24|a&16777215;a=(e&16777215)+(u&16777215)+9;b=(a>>>24)+(e>>>24)+(u>>>24)+0+((f&65535)<<8)+((v&65535)<<8)+0;f=((b>>>24)+(f>>>16)+(v>>>16)+0<<16)+(b>>8&65535);e=b<<24|a&16777215;a=(g&16777215)+(c&16777215);b=(a>>>24)+(g>>>24)+(c>>>24)+((l&65535)<<8)+((d&65535)<<8);l=((b>>>24)+(l>>>16)+(d>>>16)<<16)+
(b>>8&65535);g=b<<24|a&16777215;a=d;d=(d<<25|c>>>7)^l;c=(c<<25|a>>>7)^g;a=(h&16777215)+(e&16777215);b=(a>>>24)+(h>>>24)+(e>>>24)+((k&65535)<<8)+((f&65535)<<8);k=((b>>>24)+(k>>>16)+(f>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=f;f=(e<<1|f>>>31)^k;e=(a<<1|e>>>31)^h;a=(g&16777215)+(e&16777215);b=(a>>>24)+(g>>>24)+(e>>>24)+((l&65535)<<8)+((f&65535)<<8);l=((b>>>24)+(l>>>16)+(f>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=f;f=(e<<14|f>>>18)^l;e=(a<<14|e>>>18)^g;a=(h&16777215)+(c&16777215);b=(a>>>24)+
(h>>>24)+(c>>>24)+((k&65535)<<8)+((d&65535)<<8);k=((b>>>24)+(k>>>16)+(d>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=d;d=(d<<12|c>>>20)^k;c=(c<<12|a>>>20)^h;a=(g&16777215)+(c&16777215);b=(a>>>24)+(g>>>24)+(c>>>24)+((l&65535)<<8)+((d&65535)<<8);l=((b>>>24)+(l>>>16)+(d>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=d;d=(c<<26|d>>>6)^l;c=(a<<26|c>>>6)^g;a=(h&16777215)+(e&16777215);b=(a>>>24)+(h>>>24)+(e>>>24)+((k&65535)<<8)+((f&65535)<<8);k=((b>>>24)+(k>>>16)+(f>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;
a=f;f=(f<<22|e>>>10)^k;e=(e<<22|a>>>10)^h;a=(g&16777215)+(e&16777215);b=(a>>>24)+(g>>>24)+(e>>>24)+((l&65535)<<8)+((f&65535)<<8);l=((b>>>24)+(l>>>16)+(f>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=f;f=e^l;e=a^g;a=(h&16777215)+(c&16777215);b=(a>>>24)+(h>>>24)+(c>>>24)+((k&65535)<<8)+((d&65535)<<8);k=((b>>>24)+(k>>>16)+(d>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=d;d=c^k;c=a^h;a=(g&16777215)+(q&16777215);b=(a>>>24)+(g>>>24)+(q>>>24)+((l&65535)<<8)+((p&65535)<<8);l=((b>>>24)+(l>>>16)+(p>>>16)<<16)+
(b>>8&65535);g=b<<24|a&16777215;a=(c&16777215)+(r&16777215)+0;b=(a>>>24)+(c>>>24)+(r>>>24)+0+((d&65535)<<8)+((t&65535)<<8)+0;d=((b>>>24)+(d>>>16)+(t>>>16)+0<<16)+(b>>8&65535);c=b<<24|a&16777215;a=(h&16777215)+(u&16777215)+0;b=(a>>>24)+(h>>>24)+(u>>>24)+0+((k&65535)<<8)+((v&65535)<<8)+0;k=((b>>>24)+(k>>>16)+(v>>>16)+0<<16)+(b>>8&65535);h=b<<24|a&16777215;a=(e&16777215)+(n&16777215)+10;b=(a>>>24)+(e>>>24)+(n>>>24)+0+((f&65535)<<8)+((m&65535)<<8)+0;f=((b>>>24)+(f>>>16)+(m>>>16)+0<<16)+(b>>8&65535);e=
b<<24|a&16777215;a=(g&16777215)+(c&16777215);b=(a>>>24)+(g>>>24)+(c>>>24)+((l&65535)<<8)+((d&65535)<<8);l=((b>>>24)+(l>>>16)+(d>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=d;d=(d<<14|c>>>18)^l;c=(c<<14|a>>>18)^g;a=(h&16777215)+(e&16777215);b=(a>>>24)+(h>>>24)+(e>>>24)+((k&65535)<<8)+((f&65535)<<8);k=((b>>>24)+(k>>>16)+(f>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=f;f=(f<<16|e>>>16)^k;e=(e<<16|a>>>16)^h;a=(g&16777215)+(e&16777215);b=(a>>>24)+(g>>>24)+(e>>>24)+((l&65535)<<8)+((f&65535)<<8);l=((b>>>
24)+(l>>>16)+(f>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=f;f=(e<<20|f>>>12)^l;e=(a<<20|e>>>12)^g;a=(h&16777215)+(c&16777215);b=(a>>>24)+(h>>>24)+(c>>>24)+((k&65535)<<8)+((d&65535)<<8);k=((b>>>24)+(k>>>16)+(d>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=d;d=(c<<25|d>>>7)^k;c=(a<<25|c>>>7)^h;a=(g&16777215)+(c&16777215);b=(a>>>24)+(g>>>24)+(c>>>24)+((l&65535)<<8)+((d&65535)<<8);l=((b>>>24)+(l>>>16)+(d>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=d;d=(d<<23|c>>>9)^l;c=(c<<23|a>>>9)^g;a=(h&16777215)+
(e&16777215);b=(a>>>24)+(h>>>24)+(e>>>24)+((k&65535)<<8)+((f&65535)<<8);k=((b>>>24)+(k>>>16)+(f>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=f;f=(e<<8|f>>>24)^k;e=(a<<8|e>>>24)^h;a=(g&16777215)+(e&16777215);b=(a>>>24)+(g>>>24)+(e>>>24)+((l&65535)<<8)+((f&65535)<<8);l=((b>>>24)+(l>>>16)+(f>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=f;f=(f<<5|e>>>27)^l;e=(e<<5|a>>>27)^g;a=(h&16777215)+(c&16777215);b=(a>>>24)+(h>>>24)+(c>>>24)+((k&65535)<<8)+((d&65535)<<8);k=((b>>>24)+(k>>>16)+(d>>>16)<<16)+(b>>8&
65535);h=b<<24|a&16777215;a=d;d=(c<<5|d>>>27)^k;c=(a<<5|c>>>27)^h;a=(g&16777215)+(r&16777215);b=(a>>>24)+(g>>>24)+(r>>>24)+((l&65535)<<8)+((t&65535)<<8);l=((b>>>24)+(l>>>16)+(t>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=(c&16777215)+(u&16777215)+0;b=(a>>>24)+(c>>>24)+(u>>>24)+0+((d&65535)<<8)+((v&65535)<<8)+0;d=((b>>>24)+(d>>>16)+(v>>>16)+0<<16)+(b>>8&65535);c=b<<24|a&16777215;a=(h&16777215)+(n&16777215)+0;b=(a>>>24)+(h>>>24)+(n>>>24)+0+((k&65535)<<8)+((m&65535)<<8)+0;k=((b>>>24)+(k>>>16)+(m>>>
16)+0<<16)+(b>>8&65535);h=b<<24|a&16777215;a=(e&16777215)+(w&16777215)+11;b=(a>>>24)+(e>>>24)+(w>>>24)+0+((f&65535)<<8)+((x&65535)<<8)+0;f=((b>>>24)+(f>>>16)+(x>>>16)+0<<16)+(b>>8&65535);e=b<<24|a&16777215;a=(g&16777215)+(c&16777215);b=(a>>>24)+(g>>>24)+(c>>>24)+((l&65535)<<8)+((d&65535)<<8);l=((b>>>24)+(l>>>16)+(d>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=d;d=(d<<25|c>>>7)^l;c=(c<<25|a>>>7)^g;a=(h&16777215)+(e&16777215);b=(a>>>24)+(h>>>24)+(e>>>24)+((k&65535)<<8)+((f&65535)<<8);k=((b>>>24)+(k>>>
16)+(f>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=f;f=(e<<1|f>>>31)^k;e=(a<<1|e>>>31)^h;a=(g&16777215)+(e&16777215);b=(a>>>24)+(g>>>24)+(e>>>24)+((l&65535)<<8)+((f&65535)<<8);l=((b>>>24)+(l>>>16)+(f>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=f;f=(e<<14|f>>>18)^l;e=(a<<14|e>>>18)^g;a=(h&16777215)+(c&16777215);b=(a>>>24)+(h>>>24)+(c>>>24)+((k&65535)<<8)+((d&65535)<<8);k=((b>>>24)+(k>>>16)+(d>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=d;d=(d<<12|c>>>20)^k;c=(c<<12|a>>>20)^h;a=(g&16777215)+(c&16777215);
b=(a>>>24)+(g>>>24)+(c>>>24)+((l&65535)<<8)+((d&65535)<<8);l=((b>>>24)+(l>>>16)+(d>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=d;d=(c<<26|d>>>6)^l;c=(a<<26|c>>>6)^g;a=(h&16777215)+(e&16777215);b=(a>>>24)+(h>>>24)+(e>>>24)+((k&65535)<<8)+((f&65535)<<8);k=((b>>>24)+(k>>>16)+(f>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=f;f=(f<<22|e>>>10)^k;e=(e<<22|a>>>10)^h;a=(g&16777215)+(e&16777215);b=(a>>>24)+(g>>>24)+(e>>>24)+((l&65535)<<8)+((f&65535)<<8);l=((b>>>24)+(l>>>16)+(f>>>16)<<16)+(b>>8&65535);g=b<<
24|a&16777215;a=f;f=e^l;e=a^g;a=(h&16777215)+(c&16777215);b=(a>>>24)+(h>>>24)+(c>>>24)+((k&65535)<<8)+((d&65535)<<8);k=((b>>>24)+(k>>>16)+(d>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=d;d=c^k;c=a^h;a=(g&16777215)+(u&16777215);b=(a>>>24)+(g>>>24)+(u>>>24)+((l&65535)<<8)+((v&65535)<<8);l=((b>>>24)+(l>>>16)+(v>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=(c&16777215)+(n&16777215)+0;b=(a>>>24)+(c>>>24)+(n>>>24)+0+((d&65535)<<8)+((m&65535)<<8)+0;d=((b>>>24)+(d>>>16)+(m>>>16)+0<<16)+(b>>8&65535);c=b<<
24|a&16777215;a=(h&16777215)+(w&16777215)+0;b=(a>>>24)+(h>>>24)+(w>>>24)+0+((k&65535)<<8)+((x&65535)<<8)+0;k=((b>>>24)+(k>>>16)+(x>>>16)+0<<16)+(b>>8&65535);h=b<<24|a&16777215;a=(e&16777215)+(q&16777215)+12;b=(a>>>24)+(e>>>24)+(q>>>24)+0+((f&65535)<<8)+((p&65535)<<8)+0;f=((b>>>24)+(f>>>16)+(p>>>16)+0<<16)+(b>>8&65535);e=b<<24|a&16777215;a=(g&16777215)+(c&16777215);b=(a>>>24)+(g>>>24)+(c>>>24)+((l&65535)<<8)+((d&65535)<<8);l=((b>>>24)+(l>>>16)+(d>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=d;d=(d<<
14|c>>>18)^l;c=(c<<14|a>>>18)^g;a=(h&16777215)+(e&16777215);b=(a>>>24)+(h>>>24)+(e>>>24)+((k&65535)<<8)+((f&65535)<<8);k=((b>>>24)+(k>>>16)+(f>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=f;f=(f<<16|e>>>16)^k;e=(e<<16|a>>>16)^h;a=(g&16777215)+(e&16777215);b=(a>>>24)+(g>>>24)+(e>>>24)+((l&65535)<<8)+((f&65535)<<8);l=((b>>>24)+(l>>>16)+(f>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=f;f=(e<<20|f>>>12)^l;e=(a<<20|e>>>12)^g;a=(h&16777215)+(c&16777215);b=(a>>>24)+(h>>>24)+(c>>>24)+((k&65535)<<8)+((d&65535)<<
8);k=((b>>>24)+(k>>>16)+(d>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=d;d=(c<<25|d>>>7)^k;c=(a<<25|c>>>7)^h;a=(g&16777215)+(c&16777215);b=(a>>>24)+(g>>>24)+(c>>>24)+((l&65535)<<8)+((d&65535)<<8);l=((b>>>24)+(l>>>16)+(d>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=d;d=(d<<23|c>>>9)^l;c=(c<<23|a>>>9)^g;a=(h&16777215)+(e&16777215);b=(a>>>24)+(h>>>24)+(e>>>24)+((k&65535)<<8)+((f&65535)<<8);k=((b>>>24)+(k>>>16)+(f>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=f;f=(e<<8|f>>>24)^k;e=(a<<8|e>>>24)^h;a=(g&
16777215)+(e&16777215);b=(a>>>24)+(g>>>24)+(e>>>24)+((l&65535)<<8)+((f&65535)<<8);l=((b>>>24)+(l>>>16)+(f>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=f;f=(f<<5|e>>>27)^l;e=(e<<5|a>>>27)^g;a=(h&16777215)+(c&16777215);b=(a>>>24)+(h>>>24)+(c>>>24)+((k&65535)<<8)+((d&65535)<<8);k=((b>>>24)+(k>>>16)+(d>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=d;d=(c<<5|d>>>27)^k;c=(a<<5|c>>>27)^h;a=(g&16777215)+(n&16777215);b=(a>>>24)+(g>>>24)+(n>>>24)+((l&65535)<<8)+((m&65535)<<8);l=((b>>>24)+(l>>>16)+(m>>>16)<<
16)+(b>>8&65535);g=b<<24|a&16777215;a=(c&16777215)+(w&16777215)+0;b=(a>>>24)+(c>>>24)+(w>>>24)+0+((d&65535)<<8)+((x&65535)<<8)+0;d=((b>>>24)+(d>>>16)+(x>>>16)+0<<16)+(b>>8&65535);c=b<<24|a&16777215;a=(h&16777215)+(q&16777215)+0;b=(a>>>24)+(h>>>24)+(q>>>24)+0+((k&65535)<<8)+((p&65535)<<8)+0;k=((b>>>24)+(k>>>16)+(p>>>16)+0<<16)+(b>>8&65535);h=b<<24|a&16777215;a=(e&16777215)+(r&16777215)+13;b=(a>>>24)+(e>>>24)+(r>>>24)+0+((f&65535)<<8)+((t&65535)<<8)+0;f=((b>>>24)+(f>>>16)+(t>>>16)+0<<16)+(b>>8&65535);
e=b<<24|a&16777215;a=(g&16777215)+(c&16777215);b=(a>>>24)+(g>>>24)+(c>>>24)+((l&65535)<<8)+((d&65535)<<8);l=((b>>>24)+(l>>>16)+(d>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=d;d=(d<<25|c>>>7)^l;c=(c<<25|a>>>7)^g;a=(h&16777215)+(e&16777215);b=(a>>>24)+(h>>>24)+(e>>>24)+((k&65535)<<8)+((f&65535)<<8);k=((b>>>24)+(k>>>16)+(f>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=f;f=(e<<1|f>>>31)^k;e=(a<<1|e>>>31)^h;a=(g&16777215)+(e&16777215);b=(a>>>24)+(g>>>24)+(e>>>24)+((l&65535)<<8)+((f&65535)<<8);l=((b>>>
24)+(l>>>16)+(f>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=f;f=(e<<14|f>>>18)^l;e=(a<<14|e>>>18)^g;a=(h&16777215)+(c&16777215);b=(a>>>24)+(h>>>24)+(c>>>24)+((k&65535)<<8)+((d&65535)<<8);k=((b>>>24)+(k>>>16)+(d>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=d;d=(d<<12|c>>>20)^k;c=(c<<12|a>>>20)^h;a=(g&16777215)+(c&16777215);b=(a>>>24)+(g>>>24)+(c>>>24)+((l&65535)<<8)+((d&65535)<<8);l=((b>>>24)+(l>>>16)+(d>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=d;d=(c<<26|d>>>6)^l;c=(a<<26|c>>>6)^g;a=(h&16777215)+
(e&16777215);b=(a>>>24)+(h>>>24)+(e>>>24)+((k&65535)<<8)+((f&65535)<<8);k=((b>>>24)+(k>>>16)+(f>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=f;f=(f<<22|e>>>10)^k;e=(e<<22|a>>>10)^h;a=(g&16777215)+(e&16777215);b=(a>>>24)+(g>>>24)+(e>>>24)+((l&65535)<<8)+((f&65535)<<8);l=((b>>>24)+(l>>>16)+(f>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=f;f=e^l;e=a^g;a=(h&16777215)+(c&16777215);b=(a>>>24)+(h>>>24)+(c>>>24)+((k&65535)<<8)+((d&65535)<<8);k=((b>>>24)+(k>>>16)+(d>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;
a=d;d=c^k;c=a^h;a=(g&16777215)+(w&16777215);b=(a>>>24)+(g>>>24)+(w>>>24)+((l&65535)<<8)+((x&65535)<<8);l=((b>>>24)+(l>>>16)+(x>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=(c&16777215)+(q&16777215)+0;b=(a>>>24)+(c>>>24)+(q>>>24)+0+((d&65535)<<8)+((p&65535)<<8)+0;d=((b>>>24)+(d>>>16)+(p>>>16)+0<<16)+(b>>8&65535);c=b<<24|a&16777215;a=(h&16777215)+(r&16777215)+0;b=(a>>>24)+(h>>>24)+(r>>>24)+0+((k&65535)<<8)+((t&65535)<<8)+0;k=((b>>>24)+(k>>>16)+(t>>>16)+0<<16)+(b>>8&65535);h=b<<24|a&16777215;a=(e&16777215)+
(u&16777215)+14;b=(a>>>24)+(e>>>24)+(u>>>24)+0+((f&65535)<<8)+((v&65535)<<8)+0;f=((b>>>24)+(f>>>16)+(v>>>16)+0<<16)+(b>>8&65535);e=b<<24|a&16777215;a=(g&16777215)+(c&16777215);b=(a>>>24)+(g>>>24)+(c>>>24)+((l&65535)<<8)+((d&65535)<<8);l=((b>>>24)+(l>>>16)+(d>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=d;d=(d<<14|c>>>18)^l;c=(c<<14|a>>>18)^g;a=(h&16777215)+(e&16777215);b=(a>>>24)+(h>>>24)+(e>>>24)+((k&65535)<<8)+((f&65535)<<8);k=((b>>>24)+(k>>>16)+(f>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=f;
f=(f<<16|e>>>16)^k;e=(e<<16|a>>>16)^h;a=(g&16777215)+(e&16777215);b=(a>>>24)+(g>>>24)+(e>>>24)+((l&65535)<<8)+((f&65535)<<8);l=((b>>>24)+(l>>>16)+(f>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=f;f=(e<<20|f>>>12)^l;e=(a<<20|e>>>12)^g;a=(h&16777215)+(c&16777215);b=(a>>>24)+(h>>>24)+(c>>>24)+((k&65535)<<8)+((d&65535)<<8);k=((b>>>24)+(k>>>16)+(d>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=d;d=(c<<25|d>>>7)^k;c=(a<<25|c>>>7)^h;a=(g&16777215)+(c&16777215);b=(a>>>24)+(g>>>24)+(c>>>24)+((l&65535)<<8)+((d&
65535)<<8);l=((b>>>24)+(l>>>16)+(d>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=d;d=(d<<23|c>>>9)^l;c=(c<<23|a>>>9)^g;a=(h&16777215)+(e&16777215);b=(a>>>24)+(h>>>24)+(e>>>24)+((k&65535)<<8)+((f&65535)<<8);k=((b>>>24)+(k>>>16)+(f>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=f;f=(e<<8|f>>>24)^k;e=(a<<8|e>>>24)^h;a=(g&16777215)+(e&16777215);b=(a>>>24)+(g>>>24)+(e>>>24)+((l&65535)<<8)+((f&65535)<<8);l=((b>>>24)+(l>>>16)+(f>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=f;f=(f<<5|e>>>27)^l;e=(e<<5|a>>>27)^
g;a=(h&16777215)+(c&16777215);b=(a>>>24)+(h>>>24)+(c>>>24)+((k&65535)<<8)+((d&65535)<<8);k=((b>>>24)+(k>>>16)+(d>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=d;d=(c<<5|d>>>27)^k;c=(a<<5|c>>>27)^h;a=(g&16777215)+(q&16777215);b=(a>>>24)+(g>>>24)+(q>>>24)+((l&65535)<<8)+((p&65535)<<8);l=((b>>>24)+(l>>>16)+(p>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=(c&16777215)+(r&16777215)+0;b=(a>>>24)+(c>>>24)+(r>>>24)+0+((d&65535)<<8)+((t&65535)<<8)+0;d=((b>>>24)+(d>>>16)+(t>>>16)+0<<16)+(b>>8&65535);c=b<<24|
a&16777215;a=(h&16777215)+(u&16777215)+0;b=(a>>>24)+(h>>>24)+(u>>>24)+0+((k&65535)<<8)+((v&65535)<<8)+0;k=((b>>>24)+(k>>>16)+(v>>>16)+0<<16)+(b>>8&65535);h=b<<24|a&16777215;a=(e&16777215)+(n&16777215)+15;b=(a>>>24)+(e>>>24)+(n>>>24)+0+((f&65535)<<8)+((m&65535)<<8)+0;f=((b>>>24)+(f>>>16)+(m>>>16)+0<<16)+(b>>8&65535);e=b<<24|a&16777215;a=(g&16777215)+(c&16777215);b=(a>>>24)+(g>>>24)+(c>>>24)+((l&65535)<<8)+((d&65535)<<8);l=((b>>>24)+(l>>>16)+(d>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=d;d=(d<<25|
c>>>7)^l;c=(c<<25|a>>>7)^g;a=(h&16777215)+(e&16777215);b=(a>>>24)+(h>>>24)+(e>>>24)+((k&65535)<<8)+((f&65535)<<8);k=((b>>>24)+(k>>>16)+(f>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=f;f=(e<<1|f>>>31)^k;e=(a<<1|e>>>31)^h;a=(g&16777215)+(e&16777215);b=(a>>>24)+(g>>>24)+(e>>>24)+((l&65535)<<8)+((f&65535)<<8);l=((b>>>24)+(l>>>16)+(f>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=f;f=(e<<14|f>>>18)^l;e=(a<<14|e>>>18)^g;a=(h&16777215)+(c&16777215);b=(a>>>24)+(h>>>24)+(c>>>24)+((k&65535)<<8)+((d&65535)<<
8);k=((b>>>24)+(k>>>16)+(d>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=d;d=(d<<12|c>>>20)^k;c=(c<<12|a>>>20)^h;a=(g&16777215)+(c&16777215);b=(a>>>24)+(g>>>24)+(c>>>24)+((l&65535)<<8)+((d&65535)<<8);l=((b>>>24)+(l>>>16)+(d>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=d;d=(c<<26|d>>>6)^l;c=(a<<26|c>>>6)^g;a=(h&16777215)+(e&16777215);b=(a>>>24)+(h>>>24)+(e>>>24)+((k&65535)<<8)+((f&65535)<<8);k=((b>>>24)+(k>>>16)+(f>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=f;f=(f<<22|e>>>10)^k;e=(e<<22|a>>>10)^h;
a=(g&16777215)+(e&16777215);b=(a>>>24)+(g>>>24)+(e>>>24)+((l&65535)<<8)+((f&65535)<<8);l=((b>>>24)+(l>>>16)+(f>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=f;f=e^l;e=a^g;a=(h&16777215)+(c&16777215);b=(a>>>24)+(h>>>24)+(c>>>24)+((k&65535)<<8)+((d&65535)<<8);k=((b>>>24)+(k>>>16)+(d>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=d;d=c^k;c=a^h;a=(g&16777215)+(r&16777215);b=(a>>>24)+(g>>>24)+(r>>>24)+((l&65535)<<8)+((t&65535)<<8);l=((b>>>24)+(l>>>16)+(t>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=(c&16777215)+
(u&16777215)+0;b=(a>>>24)+(c>>>24)+(u>>>24)+0+((d&65535)<<8)+((v&65535)<<8)+0;d=((b>>>24)+(d>>>16)+(v>>>16)+0<<16)+(b>>8&65535);c=b<<24|a&16777215;a=(h&16777215)+(n&16777215)+0;b=(a>>>24)+(h>>>24)+(n>>>24)+0+((k&65535)<<8)+((m&65535)<<8)+0;k=((b>>>24)+(k>>>16)+(m>>>16)+0<<16)+(b>>8&65535);h=b<<24|a&16777215;a=(e&16777215)+(w&16777215)+16;b=(a>>>24)+(e>>>24)+(w>>>24)+0+((f&65535)<<8)+((x&65535)<<8)+0;f=((b>>>24)+(f>>>16)+(x>>>16)+0<<16)+(b>>8&65535);e=b<<24|a&16777215;a=(g&16777215)+(c&16777215);b=
(a>>>24)+(g>>>24)+(c>>>24)+((l&65535)<<8)+((d&65535)<<8);l=((b>>>24)+(l>>>16)+(d>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=d;d=(d<<14|c>>>18)^l;c=(c<<14|a>>>18)^g;a=(h&16777215)+(e&16777215);b=(a>>>24)+(h>>>24)+(e>>>24)+((k&65535)<<8)+((f&65535)<<8);k=((b>>>24)+(k>>>16)+(f>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=f;f=(f<<16|e>>>16)^k;e=(e<<16|a>>>16)^h;a=(g&16777215)+(e&16777215);b=(a>>>24)+(g>>>24)+(e>>>24)+((l&65535)<<8)+((f&65535)<<8);l=((b>>>24)+(l>>>16)+(f>>>16)<<16)+(b>>8&65535);g=b<<
24|a&16777215;a=f;f=(e<<20|f>>>12)^l;e=(a<<20|e>>>12)^g;a=(h&16777215)+(c&16777215);b=(a>>>24)+(h>>>24)+(c>>>24)+((k&65535)<<8)+((d&65535)<<8);k=((b>>>24)+(k>>>16)+(d>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=d;d=(c<<25|d>>>7)^k;c=(a<<25|c>>>7)^h;a=(g&16777215)+(c&16777215);b=(a>>>24)+(g>>>24)+(c>>>24)+((l&65535)<<8)+((d&65535)<<8);l=((b>>>24)+(l>>>16)+(d>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=d;d=(d<<23|c>>>9)^l;c=(c<<23|a>>>9)^g;a=(h&16777215)+(e&16777215);b=(a>>>24)+(h>>>24)+(e>>>24)+
((k&65535)<<8)+((f&65535)<<8);k=((b>>>24)+(k>>>16)+(f>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=f;f=(e<<8|f>>>24)^k;e=(a<<8|e>>>24)^h;a=(g&16777215)+(e&16777215);b=(a>>>24)+(g>>>24)+(e>>>24)+((l&65535)<<8)+((f&65535)<<8);l=((b>>>24)+(l>>>16)+(f>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=f;f=(f<<5|e>>>27)^l;e=(e<<5|a>>>27)^g;a=(h&16777215)+(c&16777215);b=(a>>>24)+(h>>>24)+(c>>>24)+((k&65535)<<8)+((d&65535)<<8);k=((b>>>24)+(k>>>16)+(d>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=d;d=(c<<5|d>>>
27)^k;c=(a<<5|c>>>27)^h;a=(g&16777215)+(u&16777215);b=(a>>>24)+(g>>>24)+(u>>>24)+((l&65535)<<8)+((v&65535)<<8);l=((b>>>24)+(l>>>16)+(v>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=(c&16777215)+(n&16777215)+0;b=(a>>>24)+(c>>>24)+(n>>>24)+0+((d&65535)<<8)+((m&65535)<<8)+0;d=((b>>>24)+(d>>>16)+(m>>>16)+0<<16)+(b>>8&65535);c=b<<24|a&16777215;a=(h&16777215)+(w&16777215)+0;b=(a>>>24)+(h>>>24)+(w>>>24)+0+((k&65535)<<8)+((x&65535)<<8)+0;k=((b>>>24)+(k>>>16)+(x>>>16)+0<<16)+(b>>8&65535);h=b<<24|a&16777215;
a=(e&16777215)+(q&16777215)+17;b=(a>>>24)+(e>>>24)+(q>>>24)+0+((f&65535)<<8)+((p&65535)<<8)+0;f=((b>>>24)+(f>>>16)+(p>>>16)+0<<16)+(b>>8&65535);e=b<<24|a&16777215;a=(g&16777215)+(c&16777215);b=(a>>>24)+(g>>>24)+(c>>>24)+((l&65535)<<8)+((d&65535)<<8);l=((b>>>24)+(l>>>16)+(d>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=d;d=(d<<25|c>>>7)^l;c=(c<<25|a>>>7)^g;a=(h&16777215)+(e&16777215);b=(a>>>24)+(h>>>24)+(e>>>24)+((k&65535)<<8)+((f&65535)<<8);k=((b>>>24)+(k>>>16)+(f>>>16)<<16)+(b>>8&65535);h=b<<24|a&
16777215;a=f;f=(e<<1|f>>>31)^k;e=(a<<1|e>>>31)^h;a=(g&16777215)+(e&16777215);b=(a>>>24)+(g>>>24)+(e>>>24)+((l&65535)<<8)+((f&65535)<<8);l=((b>>>24)+(l>>>16)+(f>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=f;f=(e<<14|f>>>18)^l;e=(a<<14|e>>>18)^g;a=(h&16777215)+(c&16777215);b=(a>>>24)+(h>>>24)+(c>>>24)+((k&65535)<<8)+((d&65535)<<8);k=((b>>>24)+(k>>>16)+(d>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=d;d=(d<<12|c>>>20)^k;c=(c<<12|a>>>20)^h;a=(g&16777215)+(c&16777215);b=(a>>>24)+(g>>>24)+(c>>>24)+((l&
65535)<<8)+((d&65535)<<8);l=((b>>>24)+(l>>>16)+(d>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=d;d=(c<<26|d>>>6)^l;c=(a<<26|c>>>6)^g;a=(h&16777215)+(e&16777215);b=(a>>>24)+(h>>>24)+(e>>>24)+((k&65535)<<8)+((f&65535)<<8);k=((b>>>24)+(k>>>16)+(f>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=f;f=(f<<22|e>>>10)^k;e=(e<<22|a>>>10)^h;a=(g&16777215)+(e&16777215);b=(a>>>24)+(g>>>24)+(e>>>24)+((l&65535)<<8)+((f&65535)<<8);l=((b>>>24)+(l>>>16)+(f>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=f;f=e^l;e=a^g;a=
(h&16777215)+(c&16777215);b=(a>>>24)+(h>>>24)+(c>>>24)+((k&65535)<<8)+((d&65535)<<8);k=((b>>>24)+(k>>>16)+(d>>>16)<<16)+(b>>8&65535);h=b<<24|a&16777215;a=d;d=c^k;c=a^h;a=(g&16777215)+(n&16777215);b=(a>>>24)+(g>>>24)+(n>>>24)+((l&65535)<<8)+((m&65535)<<8);l=((b>>>24)+(l>>>16)+(m>>>16)<<16)+(b>>8&65535);g=b<<24|a&16777215;a=(c&16777215)+(w&16777215)+0;b=(a>>>24)+(c>>>24)+(w>>>24)+0+((d&65535)<<8)+((x&65535)<<8)+0;d=((b>>>24)+(d>>>16)+(x>>>16)+0<<16)+(b>>8&65535);c=b<<24|a&16777215;a=(h&16777215)+(q&
16777215)+0;b=(a>>>24)+(h>>>24)+(q>>>24)+0+((k&65535)<<8)+((p&65535)<<8)+0;k=((b>>>24)+(k>>>16)+(p>>>16)+0<<16)+(b>>8&65535);h=b<<24|a&16777215;a=(e&16777215)+(r&16777215)+18;b=(a>>>24)+(e>>>24)+(r>>>24)+0+((f&65535)<<8)+((t&65535)<<8)+0;y[0]=g;y[1]=l;y[2]=c;y[3]=d;y[4]=h;y[5]=k;y[6]=b<<24|a&16777215;y[7]=((b>>>24)+(f>>>16)+(t>>>16)+0<<16)+(b>>8&65535)};"undefined"!==typeof exports&&(exports.h$Threefish_256_Process_Block=h$Threefish_256_Process_Block);
/* Copyright (C) 1991-2017 Free Software Foundation, Inc.
   This file is part of the GNU C Library.

   The GNU C Library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2.1 of the License, or (at your option) any later version.

   The GNU C Library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public
   License along with the GNU C Library; if not, see
   <http://www.gnu.org/licenses/>.  */
/* This header is separate from features.h so that the compiler can
   include it implicitly at the start of every compilation.  It must
   not itself include <features.h> or any other header that includes
   <features.h> because the implicit include comes before any feature
   test macros that may be defined in a source file before it first
   explicitly includes a system header.  GCC knows the name of this
   header in order to preinclude it.  */
/* glibc's intent is to support the IEC 559 math functionality, real
   and complex.  If the GCC (4.9 and later) predefined macros
   specifying compiler intent are available, use them to determine
   whether the overall intent is to support these features; otherwise,
   presume an older compiler has intent to support these features and
   define these macros by default.  */
/* wchar_t uses Unicode 8.0.0.  Version 8.0 of the Unicode Standard is
   synchronized with ISO/IEC 10646:2014, plus Amendment 1 (published
   2015-05-15).  */
/* We do not support C11 <threads.h>.  */
// values defined in Gen2.ClosureInfo
// thread status
/*
 * low-level heap object manipulation macros
 */
// GHCJS.Prim.JSVal
// GHCJS.Prim.JSException
// Exception dictionary for JSException
// SomeException
// GHC.Ptr.Ptr
// GHC.Integer.GMP.Internals
// Data.Maybe.Maybe
// #define HS_NOTHING h$nothing
// Data.List
// Data.Text
// Data.Text.Lazy
// black holes
// can we skip the indirection for black holes?
// resumable thunks
// general deconstruction
// retrieve  a numeric value that's possibly stored as an indirection
// generic lazy values
// generic data constructors and selectors
// unboxed tuple returns
// #define RETURN_UBX_TUP1(x) return x;
function h$_hs_text_memcpy(dst_v,dst_o2,src_v,src_o2,n) {
  return h$memcpy(dst_v,2*dst_o2,src_v,2*src_o2,2*n);
}
function h$_hs_text_memcmp(a_v,a_o2,b_v,b_o2,n) {
  return h$memcmp(a_v,2*a_o2,b_v,2*b_o2,2*n);
}
// decoder below adapted from cbits/cbits.c in the text package
var h$_text_utf8d =
   [
  /*
   * The first part of the table maps bytes to character classes that
   * to reduce the size of the transition table and create bitmasks.
   */
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1, 9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,
   7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7, 7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,
   8,8,2,2,2,2,2,2,2,2,2,2,2,2,2,2, 2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,
  10,3,3,3,3,3,3,3,3,3,3,3,3,4,3,3, 11,6,6,6,5,8,8,8,8,8,8,8,8,8,8,8,
  /*
   * The second part is a transition table that maps a combination of
   * a state of the automaton and a character class to a state.
   */
   0,12,24,36,60,96,84,12,12,12,48,72, 12,12,12,12,12,12,12,12,12,12,12,12,
  12, 0,12,12,12,12,12, 0,12, 0,12,12, 12,24,12,12,12,12,12,24,12,24,12,12,
  12,12,12,12,12,12,12,24,12,12,12,12, 12,24,12,12,12,12,12,12,12,24,12,12,
  12,12,12,12,12,12,12,36,12,36,12,12, 12,36,12,12,12,12,12,36,12,36,12,12,
  12,36,12,12,12,12,12,12,12,12,12,12];
/*
 * A best-effort decoder. Runs until it hits either end of input or
 * the start of an invalid byte sequence.
 *
 * At exit, updates *destoff with the next offset to write to, and
 * returns the next source offset to read from.
 */
function h$_hs_text_decode_utf8_internal ( dest_v
                                         , destoff_v, destoff_o
                                         , src_v, src_o
                                         , src_end_v, src_end_o
                                         , s
                                         ) {
  if(src_v === null || src_end_v === null) {
    { h$ret1 = (src_end_o); return (null); };
  }
  var dsto = destoff_v.dv.getUint32(destoff_o,true) << 1;
  var srco = src_o;
  var state = s.state;
  var codepoint = s.codepoint;
  var ddv = dest_v.dv;
  var sdv = src_v.dv;
  function decode(b) {
    var type = h$_text_utf8d[b];
    codepoint = (state !== 0) ?
      (b & 0x3f) | (codepoint << 6) :
      (0xff >>> type) & b;
    state = h$_text_utf8d[256 + state + type];
    return state;
  }
  while (srco < src_end_o) {
    if(decode(sdv.getUint8(srco++)) !== 0) {
      if(state !== 12) {
        continue;
      } else {
        break;
      }
    }
    if (codepoint <= 0xffff) {
      ddv.setUint16(dsto,codepoint,true);
      dsto += 2;
    } else {
      ddv.setUint16(dsto,(0xD7C0 + (codepoint >>> 10)),true);
      ddv.setUint16(dsto+2,(0xDC00 + (codepoint & 0x3FF)),true);
      dsto += 4;
    }
    s.last = srco;
  }
  s.state = state;
  s.codepoint = codepoint;
  destoff_v.dv.setUint32(destoff_o,dsto>>1,true);
  { h$ret1 = (srco); return (src_v); };
}
function h$_hs_text_decode_utf8_state( dest_v
                                     , destoff_v, destoff_o
                                     , src_v, src_o
                                     , srcend_v, srcend_o
                                     , codepoint0_v, codepoint0_o
                                     , state0_v, state0_o
                                     ) {
  var s = { state: state0_v.dv.getUint32(state0_o, true)
          , codepoint: codepoint0_v.dv.getUint32(codepoint0_o, true)
          , last: src_o
          };
  var ret, ret1;
  { (ret) = (h$_hs_text_decode_utf8_internal ( dest_v , destoff_v, destoff_o , src_v.arr[src_o][0], src_v.arr[src_o][1] , srcend_v, srcend_o , s )); (ret1) = h$ret1; };
  src_v.arr[src_o][1] = s.last;
  state0_v.dv.setUint32(state0_o, s.state, true);
  codepoint0_v.dv.setUint32(codepoint0_o, s.codepoint, true);
  if(s.state === 12) ret1--;
  { h$ret1 = (ret1); return (ret); };
}
function h$_hs_text_decode_utf8( dest_v
                               , destoff_v, destoff_o
                               , src_v, src_o
                               , srcend_v, srcend_o
                               ) {
  /* Back up if we have an incomplete or invalid encoding */
  var s = { state: 0
          , codepoint: 0
          , last: src_o
          };
  var ret, ret1;
  { (ret) = (h$_hs_text_decode_utf8_internal ( dest_v , destoff_v, destoff_o , src_v, src_o , srcend_v, srcend_o , s )); (ret1) = h$ret1; };
  if (s.state !== 0) ret1--;
  { h$ret1 = (ret1); return (ret); };
}
/*
 * The ISO 8859-1 (aka latin-1) code points correspond exactly to the first 256 unicode
 * code-points, therefore we can trivially convert from a latin-1 encoded bytestring to
 * an UTF16 array
 */
function h$_hs_text_decode_latin1(dest_d, src_d, src_o, srcend_d, srcend_o) {
  var p = src_o;
  var d = 0;
  var su8 = src_d.u8;
  var su3 = src_d.u3;
  var du1 = dest_d.u1;
  // consume unaligned prefix
  while(p != srcend_o && p & 3) {
    du1[d++] = su8[p++];
  }
  // iterate over 32-bit aligned loads
  if(su3) {
    while (p < srcend_o - 3) {
      var w = su3[p>>2];
      du1[d++] = w & 0xff;
      du1[d++] = (w >>> 8) & 0xff;
      du1[d++] = (w >>> 16) & 0xff;
      du1[d++] = (w >>> 32) & 0xff;
      p += 4;
    }
  }
  // handle unaligned suffix
  while (p != srcend_o)
    du1[d++] = su8[p++];
}
function h$_hs_text_encode_utf8(destp_v, destp_o, src_v, srcoff, srclen) {
  var dest_v = destp_v.arr[destp_o][0];
  var dest_o = destp_v.arr[destp_o][1];
  var src = srcoff;
  var dest = dest_o;
  var srcend = src + srclen;
  var srcu1 = src_v.u1;
  if(!srcu1) throw "h$_hs_text_encode_utf8: invalid alignment for source";
  var srcu3 = src_v.u3;
  var destu8 = dest_v.u8;
  while(src < srcend) {
    // run of (aligned) ascii characters
    while(srcu3 && !(src & 1) && srcend - src >= 2) {
      var w = srcu3[src>>1];
      if(w & 0xFF80FF80) break;
      destu8[dest++] = w & 0xFFFF;
      destu8[dest++] = w >>> 16;
      src += 2;
    }
    while(src < srcend) {
      var w = srcu1[src++];
      if(w <= 0x7F) {
        destu8[dest++] = w;
        break; // go back to a stream of ASCII
      } else if(w <= 0x7FF) {
        destu8[dest++] = (w >> 6) | 0xC0;
        destu8[dest++] = (w & 0x3f) | 0x80;
      } else if(w < 0xD800 || w > 0xDBFF) {
        destu8[dest++] = (w >>> 12) | 0xE0;
        destu8[dest++] = ((w >> 6) & 0x3F) | 0x80;
        destu8[dest++] = (w & 0x3F) | 0x80;
      } else {
        var c = ((w - 0xD800) << 10) + (srcu1[src++] - 0xDC00) + 0x10000;
        destu8[dest++] = (c >>> 18) | 0xF0;
        destu8[dest++] = ((c >> 12) & 0x3F) | 0x80;
        destu8[dest++] = ((c >> 6) & 0x3F) | 0x80;
        destu8[dest++] = (c & 0x3F) | 0x80;
      }
    }
  }
  destp_v.arr[destp_o][1] = dest;
}
/* Copyright (C) 1991-2017 Free Software Foundation, Inc.
   This file is part of the GNU C Library.

   The GNU C Library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2.1 of the License, or (at your option) any later version.

   The GNU C Library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public
   License along with the GNU C Library; if not, see
   <http://www.gnu.org/licenses/>.  */
/* This header is separate from features.h so that the compiler can
   include it implicitly at the start of every compilation.  It must
   not itself include <features.h> or any other header that includes
   <features.h> because the implicit include comes before any feature
   test macros that may be defined in a source file before it first
   explicitly includes a system header.  GCC knows the name of this
   header in order to preinclude it.  */
/* glibc's intent is to support the IEC 559 math functionality, real
   and complex.  If the GCC (4.9 and later) predefined macros
   specifying compiler intent are available, use them to determine
   whether the overall intent is to support these features; otherwise,
   presume an older compiler has intent to support these features and
   define these macros by default.  */
/* wchar_t uses Unicode 8.0.0.  Version 8.0 of the Unicode Standard is
   synchronized with ISO/IEC 10646:2014, plus Amendment 1 (published
   2015-05-15).  */
/* We do not support C11 <threads.h>.  */
/* FNV-1 hash
 *
 * The FNV-1 hash description: http://isthe.com/chongo/tech/comp/fnv/
 * The FNV-1 hash is public domain: http://isthe.com/chongo/tech/comp/fnv/#public_domain
 */
function h$hashable_fnv_hash_offset(str_a, o, len, hash) {
  return h$hashable_fnv_hash(str_a, o, len, hash);
}
function h$hashable_fnv_hash(str_d, str_o, len, hash) {
  if(len > 0) {
    var d = str_d.u8;
    for(var i=0;i<len;i++) {
      hash = h$mulInt32(hash, 16777619) ^ d[str_o+i];
    }
  }
  return hash;
}
// int hashable_getRandomBytes(unsigned char *dest, int nbytes)
function h$hashable_getRandomBytes(dest_d, dest_o, len) {
  if(len > 0) {
    var d = dest_d.u8;
    for(var i=0;i<len;i++) {
      d[dest_o+i] = Math.floor(Math.random() * 256);
    }
  }
  return len;
}
/* Copyright (C) 1991-2017 Free Software Foundation, Inc.
   This file is part of the GNU C Library.

   The GNU C Library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2.1 of the License, or (at your option) any later version.

   The GNU C Library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public
   License along with the GNU C Library; if not, see
   <http://www.gnu.org/licenses/>.  */
/* This header is separate from features.h so that the compiler can
   include it implicitly at the start of every compilation.  It must
   not itself include <features.h> or any other header that includes
   <features.h> because the implicit include comes before any feature
   test macros that may be defined in a source file before it first
   explicitly includes a system header.  GCC knows the name of this
   header in order to preinclude it.  */
/* glibc's intent is to support the IEC 559 math functionality, real
   and complex.  If the GCC (4.9 and later) predefined macros
   specifying compiler intent are available, use them to determine
   whether the overall intent is to support these features; otherwise,
   presume an older compiler has intent to support these features and
   define these macros by default.  */
/* wchar_t uses Unicode 8.0.0.  Version 8.0 of the Unicode Standard is
   synchronized with ISO/IEC 10646:2014, plus Amendment 1 (published
   2015-05-15).  */
/* We do not support C11 <threads.h>.  */
// values defined in Gen2.ClosureInfo
// thread status
/*
 * low-level heap object manipulation macros
 */
// GHCJS.Prim.JSVal
// GHCJS.Prim.JSException
// Exception dictionary for JSException
// SomeException
// GHC.Ptr.Ptr
// GHC.Integer.GMP.Internals
// Data.Maybe.Maybe
// #define HS_NOTHING h$nothing
// Data.List
// Data.Text
// Data.Text.Lazy
// black holes
// can we skip the indirection for black holes?
// resumable thunks
// general deconstruction
// retrieve  a numeric value that's possibly stored as an indirection
// generic lazy values
// generic data constructors and selectors
// unboxed tuple returns
// #define RETURN_UBX_TUP1(x) return x;
// JS Objects stuff
function h$isFloat (n) {
  return n===+n && n!==(n|0);
}
function h$isInteger (n) {
  return n===+n && n===(n|0);
}
/*
        -- 0 - null, 1 - integer,
        -- 2 - float, 3 - bool,
        -- 4 - string, 5 - array
        -- 6 - object
*/
function h$typeOf(o) {
    if (!(o instanceof Object)) {
        if (o == null) {
            return 0;
        } else if (typeof o == 'number') {
            if (h$isInteger(o)) {
                return 1;
            } else {
                return 2;
            }
        } else if (typeof o == 'boolean') {
            return 3;
        } else {
            return 4;
        }
    } else {
        if (Object.prototype.toString.call(o) == '[object Array]') {
            // it's an array
            return 5;
        } else if (!o) {
            // null 
            return 0;
        } else {
            // it's an object
            return 6;
        }
    }
}
function h$flattenObj(o) {
    var l = [], i = 0;
    for (var prop in o) {
        l[i++] = [prop, o[prop]];
    }
    return l;
}
/*

  build an object from key/value pairs:
    var obj = h$buildObject(key1, val1, key2, val2, ...);

  note: magic name:
    invocations of this function are replaced by object literals wherever
    possible

 */
function h$buildObject() {
    var r = {}, l = arguments.length;
    for(var i = 0; i < l; i += 2) {
        var k = arguments[i], v = arguments[i+1];
        r[k] = v;
    }
    return r;
}
// same as above, but from a list: [k1,v1,k2,v2,...]
function h$buildObjectFromList(xs) {
    var r = {}, k, v, t;
    while(((xs).f === h$ghczmprimZCGHCziTypesziZC_con_e)) {
        xs = ((xs).d2);
        t = ((xs).d2);
        if(((t).f === h$ghczmprimZCGHCziTypesziZC_con_e)) {
            k = ((xs).d1);
            v = ((t).d1);
            xs = ((t).d2);
            r[k] = v;
        } else {
            return r;
        }
    }
    return r;
}
// same as above, but from a list of tuples [(k1,v1),(k2,v2),...]
function h$buildObjectFromTupList(xs) {
    var r = {};
    while(((xs).f === h$ghczmprimZCGHCziTypesziZC_con_e)) {
 var h = ((xs).d1);
 xs = ((xs).d2);
 r[((((h).d1)).d1)] = ((((h).d2)).d1);
    }
    return r;
}
/* Copyright (C) 1991-2017 Free Software Foundation, Inc.
   This file is part of the GNU C Library.

   The GNU C Library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2.1 of the License, or (at your option) any later version.

   The GNU C Library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public
   License along with the GNU C Library; if not, see
   <http://www.gnu.org/licenses/>.  */
/* This header is separate from features.h so that the compiler can
   include it implicitly at the start of every compilation.  It must
   not itself include <features.h> or any other header that includes
   <features.h> because the implicit include comes before any feature
   test macros that may be defined in a source file before it first
   explicitly includes a system header.  GCC knows the name of this
   header in order to preinclude it.  */
/* glibc's intent is to support the IEC 559 math functionality, real
   and complex.  If the GCC (4.9 and later) predefined macros
   specifying compiler intent are available, use them to determine
   whether the overall intent is to support these features; otherwise,
   presume an older compiler has intent to support these features and
   define these macros by default.  */
/* wchar_t uses Unicode 8.0.0.  Version 8.0 of the Unicode Standard is
   synchronized with ISO/IEC 10646:2014, plus Amendment 1 (published
   2015-05-15).  */
/* We do not support C11 <threads.h>.  */
// values defined in Gen2.ClosureInfo
// thread status
/*
 * low-level heap object manipulation macros
 */
// GHCJS.Prim.JSVal
// GHCJS.Prim.JSException
// Exception dictionary for JSException
// SomeException
// GHC.Ptr.Ptr
// GHC.Integer.GMP.Internals
// Data.Maybe.Maybe
// #define HS_NOTHING h$nothing
// Data.List
// Data.Text
// Data.Text.Lazy
// black holes
// can we skip the indirection for black holes?
// resumable thunks
// general deconstruction
// retrieve  a numeric value that's possibly stored as an indirection
// generic lazy values
// generic data constructors and selectors
// unboxed tuple returns
// #define RETURN_UBX_TUP1(x) return x;
// translated from bytestring cbits/fpstring.c
function h$fps_reverse(a_v, a_o, b_v, b_o, n) {
    if(n > 0) {
        var au8 = a_v.u8, bu8 = b_v.u8;
        for(var i=0;i<n;i++) {
            au8[a_o+n-i-1] = bu8[b_o+i];
        }
    }
}
function h$fps_intersperse(a_v,a_o,b_v,b_o,n,c) {
    if(n > 0) {
        var au8 = a_v.u8, bu8 = b_v.u8, dst_o = a_o;
        for(var i=0;i<n-1;i++) {
            au8[dst_o] = bu8[b_o+i];
            au8[dst_o+1] = c;
            dst_o += 2;
        }
        au8[dst_o] = bu8[b_o+n-1];
    }
}
function h$fps_maximum(a_v,a_o,n) {
    if(n > 0) {
        var au8 = a_v.u8, max = au8[a_o];
        for(var i=1;i<n;i++) {
            var c = au8[a_o+i];
            if(c > max) { max = c; }
        }
        return max;
    }
    return 0;
}
function h$fps_minimum(a_v,a_o,n) {
    if(n > 0) {
        var au8 = a_v.u8, min = a_v.u8[a_o];
        for(var i=1;i<n;i++) {
            var c = au8[a_o+i];
            if(c < min) { min = c; }
        }
        return min;
    }
    return 255;
}
function h$fps_count(a_v,a_o,n,c) {
    if(n > 0) {
        var au8 = a_v.u8, count = 0;
        for(var i=0;i<n;i++) {
            if(au8[a_o+i] === c) { count++; }
        }
        return count|0;
    }
    return 0;
}
function h$fps_memcpy_offsets(dst_d, dst_o, dst_off
                              , src_d, src_o, src_off, n) {
    return memcpy(dst_d, dst_o + dst_off, src_d, src_o + src_off, n);
}
// translated from bytestring cbits/itoa.c
var h$_hs_bytestring_digits = [48,49,50,51,52,53,54,55,56,57,97,98,99,100,101,102]; // 0123456789abcdef
var h$_hs_bytestring_l10 = goog.math.Long.fromBits(10, 0);
// signed integers
function h$_hs_bytestring_int_dec(x, buf_d, buf_o) {
    var c, ptr = buf_o, next_free, x_tmp;
    var bu8 = buf_d.u8;
    // we cannot negate directly as  0 - (minBound :: Int) = minBound
    if(x < 0) {
        bu8[ptr++] = 45; // '-'
        buf_o++;
        x_tmp = x;
        x = (x / 10) | 0;
        bu8[ptr++] = h$_hs_bytestring_digits[x * 10 - x_tmp];
        if(x === 0) {
            { h$ret1 = (ptr); return (buf_d); };
        } else {
            x = -x;
        }
    }
    // encode positive number as little-endian decimal
    do {
        x_tmp = x;
        x = (x / 10) | 0;
        bu8[ptr++] = h$_hs_bytestring_digits[x_tmp - x * 10];
    } while (x);
    next_free = ptr--;
    while(buf_o < ptr) {
        c = bu8[ptr];
        bu8[ptr--] = bu8[buf_o];
        bu8[buf_o++] = c;
    }
    { h$ret1 = (next_free); return (buf_d); };
}
// signed long long ints (64 bit integers)
function h$_hs_bytestring_long_long_int_dec(x_a, x_b, buf_d, buf_o) {
    var l10 = h$_hs_bytestring_l10;
    var x = goog.math.Long.fromBits(x_b, x_a);
    var c, ptr = buf_o, next_free;
    var bu8 = buf_d.u8;
    // we cannot negate directly as  0 - (minBound :: Int) = minBound
    if(x.isNegative()) {
        bu8[ptr++] = 45; // '-';
        buf_o++;
        x_tmp = x;
        x = x.div(l10);
        bu8[ptr++] = h$_hs_bytestring_digits[x.multiply(l10).subtract(x_tmp).getLowBits()];
        if(x.isZero()) {
            { h$ret1 = (ptr); return (buf_d); };
        } else {
            x = x.negate();
        }
    }
    // encode positive number as little-endian decimal
    do {
        x_tmp = x;
        x = x.div(l10);
        bu8[ptr++] = h$_hs_bytestring_digits[x_tmp.subtract(x.multiply(l10))];
    } while (!x.isZero());
    // reverse written digits
    next_free = ptr--;
    while(buf_o < ptr) {
        c = bu8[ptr];
        bu8[ptr--] = bu8[buf_o];
        bu8[buf_o++] = c;
    }
    { h$ret1 = (next_free); return (buf_d); };
}
// unsigned integers
function h$_hs_bytestring_uint_dec(x, buf_d, buf_o) {
    var c, ptr = buf_o, next_free;
    var bu8 = buf_d.u8;
    var x_tmp;
    if(x < 0) x += 4294967296;
    do {
        x_tmp = x;
        x = (x / 10) | 0;
        bu8[ptr++] = h$_hs_bytestring_digits[x_tmp - x * 10];
    } while(x);
    next_free = ptr--;
    while(buf_o < ptr) {
        c = bu8[ptr];
        bu8[ptr--] = bu8[buf_o];
        bu8[buf_o++] = c;
    }
    { h$ret1 = (next_free); return (buf_d); };
}
function h$_hs_bytestring_long_long_uint_dec(x_a, x_b, buf_d, buf_o) {
    var c, ptr = buf_o, next_free;
    var bu8 = buf_d.u8;
    var x = h$ghcjsbn_mkBigNat_ww(x_a, x_b), q = [], r = [];
    // encode positive number as little-endian decimal
    do {
        h$ghcjsbn_quotRem_bw(q, r, x, 10);
        x = q;
        bu8[ptr++] = h$_hs_bytestring_digits[h$ghcjsbn_toInt_b(r)];
    } while(!h$ghcjsbn_isZero_b(x));
    // reverse written digits;
    next_free = ptr--;
    while(buf_o < ptr) {
        c = bu8[ptr];
        bu8[ptr--] = bu8[buf_o];
        bu8[buf_o++] = c;
    }
    { h$ret1 = (next_free); return (buf_d); };
}
// Padded, decimal, positive integers for the decimal output of bignums
///////////////////////////////////////////////////////////////////////
// Padded (9 digits), decimal, positive int:
// We will use it with numbers that fit in 31 bits; i.e., numbers smaller than
// 10^9, as "31 * log 2 / log 10 = 9.33"
function h$_hs_bytestring_int_dec_padded9(x, buf_d, buf_o) {
    var max_width_int32_dec = 9;
    var ptr = buf_o + max_width_int32_dec;
    var bu8 = buf_d.u8;
    var x_tmp;
    // encode positive number as little-endian decimal
    do {
        x_tmp = x;
        x = (x / 10) | 0;
        bu8[--ptr] = h$_hs_bytestring_digits[x_tmp - x * 10];
    } while(x);
    // pad beginning
    while (buf_o < ptr) { bu8[--ptr] = 48; }
}
// Padded (19 digits), decimal, positive long long int:
// We will use it with numbers that fit in 63 bits; i.e., numbers smaller than
// 10^18, as "63 * log 2 / log 10 = 18.96"
function h$_hs_bytestring_long_long_int_dec_padded18(x_a, x_b, buf_d, buf_o) {
    var l10 = h$_hs_bytestring_l10;
    var max_width_int64_dec = 18;
    var ptr = buf_o + max_width_int64_dec;
    var bu8 = buf_d.u8;
    var x = goog.math.Long.fromBits(x_b, x_a);
    // encode positive number as little-endian decimal
    do {
        x_tmp = x;
        x = x.div(l10);
        bu8[--ptr] = h$_hs_bytestring_digits[x_tmp.subtract(x.multiply(l10))];
    } while (!x.isZero());
    // pad beginning
    while (buf_o < ptr) { bu8[--ptr] = 48; }
}
///////////////////////
// Hexadecimal encoding
///////////////////////
// unsigned ints (32 bit words)
function h$_hs_bytestring_uint_hex(x, buf_d, buf_o) {
    var c, ptr = buf_o, next_free;
    var bu8 = buf_d.u8;
    // write hex representation in reverse order
    do {
        bu8[ptr++] = h$_hs_bytestring_digits[x & 0xf];
        x >>>= 4;
    } while(x);
    // invert written digits
    next_free = ptr--;
    while(buf_o < ptr) {
        c = bu8[ptr];
        bu8[ptr--] = bu8[buf_o];
        bu8[buf_o++] = c;
    }
    { h$ret1 = (next_free); return (buf_d); };
}
// unsigned long ints (64 bit words)
function h$_hs_bytestring_long_long_uint_hex(x_a, x_b, buf_d, buf_o) {
    // write hex representation in reverse order
    var c, ptr = buf_o, next_free;
    var bu8 = buf_d.u8;
    if(x_a === 0 && x_b === 0) {
        bu8[ptr++] = 48; // '0'
    } else {
        while(x_b !== 0) {
            bu8[ptr++] = h$_hs_bytestring_digits[x_b & 0xf];
            x_b >>>= 4;
        }
        while(x_a !== 0) {
            bu8[ptr++] = h$_hs_bytestring_digits[x_a & 0xf];
            x_a >>>= 4;
        }
    }
    // invert written digits
    next_free = ptr--;
    while(buf_o < ptr) {
        c = bu8[ptr];
        bu8[ptr--] = bu8[buf_o];
        bu8[buf_o++] = c;
    }
    { h$ret1 = (next_free); return (buf_d); };
}
/* Copyright (C) 1991-2017 Free Software Foundation, Inc.
   This file is part of the GNU C Library.

   The GNU C Library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2.1 of the License, or (at your option) any later version.

   The GNU C Library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public
   License along with the GNU C Library; if not, see
   <http://www.gnu.org/licenses/>.  */
/* This header is separate from features.h so that the compiler can
   include it implicitly at the start of every compilation.  It must
   not itself include <features.h> or any other header that includes
   <features.h> because the implicit include comes before any feature
   test macros that may be defined in a source file before it first
   explicitly includes a system header.  GCC knows the name of this
   header in order to preinclude it.  */
/* glibc's intent is to support the IEC 559 math functionality, real
   and complex.  If the GCC (4.9 and later) predefined macros
   specifying compiler intent are available, use them to determine
   whether the overall intent is to support these features; otherwise,
   presume an older compiler has intent to support these features and
   define these macros by default.  */
/* wchar_t uses Unicode 8.0.0.  Version 8.0 of the Unicode Standard is
   synchronized with ISO/IEC 10646:2014, plus Amendment 1 (published
   2015-05-15).  */
/* We do not support C11 <threads.h>.  */
function h$filepath_isWindows() {
    if(h$isNode && process.platform === 'win32') return true;
  return false;
}
/* Copyright (C) 1991-2017 Free Software Foundation, Inc.
   This file is part of the GNU C Library.

   The GNU C Library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2.1 of the License, or (at your option) any later version.

   The GNU C Library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public
   License along with the GNU C Library; if not, see
   <http://www.gnu.org/licenses/>.  */
/* This header is separate from features.h so that the compiler can
   include it implicitly at the start of every compilation.  It must
   not itself include <features.h> or any other header that includes
   <features.h> because the implicit include comes before any feature
   test macros that may be defined in a source file before it first
   explicitly includes a system header.  GCC knows the name of this
   header in order to preinclude it.  */
/* glibc's intent is to support the IEC 559 math functionality, real
   and complex.  If the GCC (4.9 and later) predefined macros
   specifying compiler intent are available, use them to determine
   whether the overall intent is to support these features; otherwise,
   presume an older compiler has intent to support these features and
   define these macros by default.  */
/* wchar_t uses Unicode 8.0.0.  Version 8.0 of the Unicode Standard is
   synchronized with ISO/IEC 10646:2014, plus Amendment 1 (published
   2015-05-15).  */
/* We do not support C11 <threads.h>.  */
/* include/HsBaseConfig.h.  Generated from HsBaseConfig.h.in by configure.  */
/* include/HsBaseConfig.h.in.  Generated from configure.ac by autoheader.  */
/* The value of E2BIG. */
/* The value of EACCES. */
/* The value of EADDRINUSE. */
/* The value of EADDRNOTAVAIL. */
/* The value of EADV. */
/* The value of EAFNOSUPPORT. */
/* The value of EAGAIN. */
/* The value of EALREADY. */
/* The value of EBADF. */
/* The value of EBADMSG. */
/* The value of EBADRPC. */
/* The value of EBUSY. */
/* The value of ECHILD. */
/* The value of ECOMM. */
/* The value of ECONNABORTED. */
/* The value of ECONNREFUSED. */
/* The value of ECONNRESET. */
/* The value of EDEADLK. */
/* The value of EDESTADDRREQ. */
/* The value of EDIRTY. */
/* The value of EDOM. */
/* The value of EDQUOT. */
/* The value of EEXIST. */
/* The value of EFAULT. */
/* The value of EFBIG. */
/* The value of EFTYPE. */
/* The value of EHOSTDOWN. */
/* The value of EHOSTUNREACH. */
/* The value of EIDRM. */
/* The value of EILSEQ. */
/* The value of EINPROGRESS. */
/* The value of EINTR. */
/* The value of EINVAL. */
/* The value of EIO. */
/* The value of EISCONN. */
/* The value of EISDIR. */
/* The value of ELOOP. */
/* The value of EMFILE. */
/* The value of EMLINK. */
/* The value of EMSGSIZE. */
/* The value of EMULTIHOP. */
/* The value of ENAMETOOLONG. */
/* The value of ENETDOWN. */
/* The value of ENETRESET. */
/* The value of ENETUNREACH. */
/* The value of ENFILE. */
/* The value of ENOBUFS. */
/* The value of ENOCIGAR. */
/* The value of ENODATA. */
/* The value of ENODEV. */
/* The value of ENOENT. */
/* The value of ENOEXEC. */
/* The value of ENOLCK. */
/* The value of ENOLINK. */
/* The value of ENOMEM. */
/* The value of ENOMSG. */
/* The value of ENONET. */
/* The value of ENOPROTOOPT. */
/* The value of ENOSPC. */
/* The value of ENOSR. */
/* The value of ENOSTR. */
/* The value of ENOSYS. */
/* The value of ENOTBLK. */
/* The value of ENOTCONN. */
/* The value of ENOTDIR. */
/* The value of ENOTEMPTY. */
/* The value of ENOTSOCK. */
/* The value of ENOTSUP. */
/* The value of ENOTTY. */
/* The value of ENXIO. */
/* The value of EOPNOTSUPP. */
/* The value of EPERM. */
/* The value of EPFNOSUPPORT. */
/* The value of EPIPE. */
/* The value of EPROCLIM. */
/* The value of EPROCUNAVAIL. */
/* The value of EPROGMISMATCH. */
/* The value of EPROGUNAVAIL. */
/* The value of EPROTO. */
/* The value of EPROTONOSUPPORT. */
/* The value of EPROTOTYPE. */
/* The value of ERANGE. */
/* The value of EREMCHG. */
/* The value of EREMOTE. */
/* The value of EROFS. */
/* The value of ERPCMISMATCH. */
/* The value of ERREMOTE. */
/* The value of ESHUTDOWN. */
/* The value of ESOCKTNOSUPPORT. */
/* The value of ESPIPE. */
/* The value of ESRCH. */
/* The value of ESRMNT. */
/* The value of ESTALE. */
/* The value of ETIME. */
/* The value of ETIMEDOUT. */
/* The value of ETOOMANYREFS. */
/* The value of ETXTBSY. */
/* The value of EUSERS. */
/* The value of EWOULDBLOCK. */
/* The value of EXDEV. */
/* The value of O_BINARY. */
/* The value of SIGINT. */
/* Define to 1 if you have the `clock_gettime' function. */
/* #undef HAVE_CLOCK_GETTIME */
/* Define to 1 if you have the <ctype.h> header file. */
/* Define if you have epoll support. */
/* #undef HAVE_EPOLL */
/* Define to 1 if you have the `epoll_ctl' function. */
/* #undef HAVE_EPOLL_CTL */
/* Define to 1 if you have the <errno.h> header file. */
/* Define to 1 if you have the `eventfd' function. */
/* #undef HAVE_EVENTFD */
/* Define to 1 if you have the <fcntl.h> header file. */
/* Define to 1 if you have the `ftruncate' function. */
/* Define to 1 if you have the `getclock' function. */
/* #undef HAVE_GETCLOCK */
/* Define to 1 if you have the `getrusage' function. */
/* Define to 1 if you have the <inttypes.h> header file. */
/* Define to 1 if you have the `iswspace' function. */
/* Define to 1 if you have the `kevent' function. */
/* Define to 1 if you have the `kevent64' function. */
/* Define if you have kqueue support. */
/* Define to 1 if you have the <langinfo.h> header file. */
/* Define to 1 if you have libcharset. */
/* Define to 1 if you have the `rt' library (-lrt). */
/* #undef HAVE_LIBRT */
/* Define to 1 if you have the <limits.h> header file. */
/* Define to 1 if the system has the type `long long'. */
/* Define to 1 if you have the `lstat' function. */
/* Define to 1 if you have the <memory.h> header file. */
/* Define if you have poll support. */
/* Define to 1 if you have the <poll.h> header file. */
/* Define to 1 if you have the <signal.h> header file. */
/* Define to 1 if you have the <stdint.h> header file. */
/* Define to 1 if you have the <stdlib.h> header file. */
/* Define to 1 if you have the <strings.h> header file. */
/* Define to 1 if you have the <string.h> header file. */
/* Define to 1 if you have the <sys/epoll.h> header file. */
/* #undef HAVE_SYS_EPOLL_H */
/* Define to 1 if you have the <sys/eventfd.h> header file. */
/* #undef HAVE_SYS_EVENTFD_H */
/* Define to 1 if you have the <sys/event.h> header file. */
/* Define to 1 if you have the <sys/resource.h> header file. */
/* Define to 1 if you have the <sys/select.h> header file. */
/* Define to 1 if you have the <sys/stat.h> header file. */
/* Define to 1 if you have the <sys/syscall.h> header file. */
/* Define to 1 if you have the <sys/timeb.h> header file. */
/* Define to 1 if you have the <sys/timers.h> header file. */
/* #undef HAVE_SYS_TIMERS_H */
/* Define to 1 if you have the <sys/times.h> header file. */
/* Define to 1 if you have the <sys/time.h> header file. */
/* Define to 1 if you have the <sys/types.h> header file. */
/* Define to 1 if you have the <sys/utsname.h> header file. */
/* Define to 1 if you have the <sys/wait.h> header file. */
/* Define to 1 if you have the <termios.h> header file. */
/* Define to 1 if you have the `times' function. */
/* Define to 1 if you have the <time.h> header file. */
/* Define to 1 if you have the <unistd.h> header file. */
/* Define to 1 if you have the <utime.h> header file. */
/* Define to 1 if you have the <wctype.h> header file. */
/* Define to 1 if you have the <windows.h> header file. */
/* #undef HAVE_WINDOWS_H */
/* Define to 1 if you have the <winsock.h> header file. */
/* #undef HAVE_WINSOCK_H */
/* Define to 1 if you have the `_chsize' function. */
/* #undef HAVE__CHSIZE */
/* Define to Haskell type for cc_t */
/* Define to Haskell type for char */
/* Define to Haskell type for clock_t */
/* Define to Haskell type for dev_t */
/* Define to Haskell type for double */
/* Define to Haskell type for float */
/* Define to Haskell type for gid_t */
/* Define to Haskell type for ino_t */
/* Define to Haskell type for int */
/* Define to Haskell type for intmax_t */
/* Define to Haskell type for intptr_t */
/* Define to Haskell type for long */
/* Define to Haskell type for long long */
/* Define to Haskell type for mode_t */
/* Define to Haskell type for nlink_t */
/* Define to Haskell type for off_t */
/* Define to Haskell type for pid_t */
/* Define to Haskell type for ptrdiff_t */
/* Define to Haskell type for rlim_t */
/* Define to Haskell type for short */
/* Define to Haskell type for signed char */
/* Define to Haskell type for sig_atomic_t */
/* Define to Haskell type for size_t */
/* Define to Haskell type for speed_t */
/* Define to Haskell type for ssize_t */
/* Define to Haskell type for suseconds_t */
/* Define to Haskell type for tcflag_t */
/* Define to Haskell type for time_t */
/* Define to Haskell type for uid_t */
/* Define to Haskell type for uintmax_t */
/* Define to Haskell type for uintptr_t */
/* Define to Haskell type for unsigned char */
/* Define to Haskell type for unsigned int */
/* Define to Haskell type for unsigned long */
/* Define to Haskell type for unsigned long long */
/* Define to Haskell type for unsigned short */
/* Define to Haskell type for useconds_t */
/* Define to Haskell type for wchar_t */
/* Define to the address where bug reports for this package should be sent. */
/* Define to the full name of this package. */
/* Define to the full name and version of this package. */
/* Define to the one symbol short name of this package. */
/* Define to the home page for this package. */
/* Define to the version of this package. */
/* The size of `kev.filter', as computed by sizeof. */
/* The size of `kev.flags', as computed by sizeof. */
/* The size of `struct MD5Context', as computed by sizeof. */
/* Define to 1 if you have the ANSI C header files. */
/* Number of bits in a file offset, on hosts where this is settable. */
/* #undef _FILE_OFFSET_BITS */
/* Define for large files, on AIX-style hosts. */
/* #undef _LARGE_FILES */
// get/set permissions for file
// set errno and return -1 on error
// masks: 1 - read
//        2 - write
//        4 - exe
//        8 - search
function h$directory_getPermissions(file, c) {
    ;
    if(h$isNode) {
        h$fs.stat(file, function(err, fs) {
            if(err) {
                h$handleErrnoC(err, -1, 0, c);
            } else {
                var m = fs.mode;
                var r = (m&4) || (m&32) || (m&256);
                var w = (m&2) || (m&16) || (m&128);
                var x = (m&1) || (m&8) || (m&64);
                var exe = x; // fixme?
                var search = x; // fixme?
                if(process.platform == 'win32') exe = true;
                c((r?1:0)|(w?2:0)|(exe?4:0)|(search?8:0));
            }
        });
    } else
        h$unsupported(-1, c);
}
function h$directory_setPermissions(file, perms, c) {
    ;
    if(h$isNode) {
        h$fs.stat(file, function(err, fs) {
            if(err) {
                h$handleErrnoC(err, -1, 0, c);
            } else {
                var r = perms & 1;
                var w = perms & 2;
                var x = perms & 4;
                var search = perms & 8;
                var m = fs.mode;
                m = r ? (m | 292) : (m & ~292);
                m = w ? (m | 146) : (m & ~146);
                m = (x || search) ? (m | 73) : (m & ~73);
                h$fs.chmod(file, function(err) {
                    h$handleErrnoC(err, -1, 0, c);
                });
            }
        });
    } else
        h$unsupported(-1, c);
}
function h$directory_copyPermissions(file1, file2, c) {
    ;
    if(h$isNode) {
        h$fs.stat(file1, function(err1, fs) {
            if(err1) {
                h$handleErrnoC(err1, -1, 0, c);
            } else {
                h$fs.chmod(file2, fs.mode, function(err2) {
                    h$handleErrnoC(err2, -1, 0, c);
                });
            }
        });
    } else
        h$unsupported(-1, c);
}
function h$directory_createDirectory(dir, c) {
    ;
    if(h$isNode) {
        h$fs.mkdir(dir, function(err) {
            h$handleErrnoC(err,-1,0,c);
        });
    } else
        h$unsupported(-1, c);
}
function h$directory_removeDirectory(dir, c) {
    ;
    if(h$isNode) {
        h$fs.rmdir(dir, function(err) {
            h$handleErrnoC(err,-1,0,c);
        });
    } else
        h$unsupported(-1, c);
}
function h$directory_removeFile(file, c) {
    ;
    if(h$isNode) {
        h$fs.unlink(file, function(err) {
            h$handleErrnoC(err,-1,0,c);
        });
    } else
        h$unsupported(-1, c);
}
function h$directory_renameDirectory(dir1, dir2, c) {
    ;
    if(h$isNode) {
        h$fs.rename(dir1, dir2, function(err) {
            h$handleErrnoC(err,-1,0,c);
        });
    } else
        h$unsupported(-1, c);
}
function h$directory_renameFile(file1, file2, c) {
    ;
    if(h$isNode) {
        h$fs.rename(file1, file2, function(err) {
            h$handleErrnoC(err,-1,0,c);
        });
    } else
        h$unsupported(-1, c);
}
function h$directory_canonicalizePath(path) {
    ;
    if(h$isNode) {
        return h$path.normalize(path);
    } else
        return path;
}
function h$directory_findExecutables(name, c) {
    ;
    if(h$isNode) {
        var result = [];
        var pathSep = process.platform === 'win32'?';':':';
        var parts = process.env['PATH'].split(pathSep);
        var exts = []; // process.platform === 'win32'?process.env['PATHEXT'].split(pathSep):[];
        exts.push(null);
        files = [];
        result = [];
        for(var i=0;i<parts.length;i++) {
            for(var j=0;j<exts.length;j++) {
                files.push(parts[i] + h$path.sep + name + (exts[j]?(exts[j]):""));
            }
        }
        var tryFile = function(n) {
            if(n >= files.length) {
                c(result);
            } else {
                ;
                h$fs.stat(files[n], function(err, fs) {
                    if(!err && ((fs.mode & 73) || process.platform === 'win32')) result.push(files[n]);
                    tryFile(n+1);
                });
            }
        }
        tryFile(0);
    } else
        c([]);
}
function h$directory_getDirectoryContents(dir,c) {
    ;
    if(h$isNode) {
        h$fs.readdir(dir, function(err, d) {
            h$handleErrnoC(err, null, d, c);
        });
    } else
        h$unsupported(null, c);
}
function h$directory_getCurrentDirectory() {
    ;
    if(h$isNode) {
        return h$handleErrno(null, function() {
            return process.cwd();
        });
    } else
        return "/";
}
function h$directory_setCurrentDirectory(dir) {
    ;
    if(h$isNode) {
        return h$handleErrnoS(-1, 0, function() {
            return process.chdir(dir);
        });
    } else
        return h$unsupported(-1);
}
function h$directory_getHomeDirectory(dir) {
    ;
    if(h$isNode) {
        return process.env['HOME'] ||
            process.env['HOMEPATH'] ||
            process.env['USERPROFILE'];
    } else
        return "/"
}
function h$directory_getAppUserDataDirectory(appName) {
    ;
    if(h$isNode) {
        if(process.env['APPDATA'])
            return process.env['APPDATA'] + h$path.sep + appName;
        if(process.env['HOME'])
            return process.env['HOME'] + h$path.sep + "." + appName;
        ;
        return "/";
    } else
        return "/";
}
function h$directory_getUserDocumentsDirectory(appName) {
    ;
    if(h$isNode) {
        if(process.env['HOME'])
            return process.env['HOME'];
        // fixme handle Windows
        ;
        return "/";
    } else
        return "/";
}
function h$directory_getTemporaryDirectory() {
    ;
    if(h$isNode) {
        return h$handleErrno(null, function() {
            return h$os.tmpdir();
        });
    } else
        return "/";
}
function h$directory_exeExtension() {
    ;
    if(h$isNode) {
        return (h$os.platform() === 'windows') ? 'exe' : '';
    } else
        return '';
}
function h$directory_getFileStatus(file, c) {
    ;
    if(h$isNode) {
        h$fs.stat(file, function(err, s) {
            h$handleErrnoC(err, null, s, c);
        });
    } else
        h$unsupported(null, c);
}
function h$directory_getFileOrSymlinkStatus(file, c) {
    ;
    if(h$isNode) {
        h$fs.lstat(file, function(err, s) {
            h$handleErrnoC(err, null, s, c);
        });
    } else
        h$unsupported(null, c);
}
function h$directory_getFileStatusAccessTime(fs) {
  ;
  return fs.atime.getTime();
}
function h$directory_getFileStatusModificationTime(fs) {
  ;
  return fs.mtime.getTime();
}
function h$directory_getFileStatusIsDirectory(fs) {
  ;
  return fs.isDirectory();
}
function h$directory_getFileStatusIsSymbolicLink(fs) {
  ;
  return fs.isSymbolicLink();
}
// fixme this doesn't really belong here
function h$chmod(path_d, path_o, m) {
    if(h$isNode) {
        var path = h$decodeUtf8z(path_d, path_o);
        ;
        h$fs.chmodSync(path, m);
        return 0;
    } else
        return h$unsupported(-1);
}
