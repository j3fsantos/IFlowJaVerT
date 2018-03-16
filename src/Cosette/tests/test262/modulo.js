// taken from ch11/11.5/11.5.3/S11.5.3_A4_T7.js

// Copyright 2009 the Sputnik authors.  All rights reserved.
// This code is governed by the BSD license found in the LICENSE file.

/**
 * The result of a ECMAScript floating-point remainder operation is determined by the rules of IEEE arithmetics
 *
 * @path ch11/11.5/11.5.3/S11.5.3_A4_T7.js
 * @description If operands neither an infinity, nor a zero, nor NaN, return x - truncate(x / y) * y
 */

function truncate(x) {
  if (x > 0) {
    return Math.floor(x);
  } else {
    return Math.ceil(x);
  }
}

//CHECK#1
var x = symb_number (n1); 
var y = symb_number (n2);

Assume((not (x = 0)) and (not (y = 0)));

var xy = x % y;
var by_hand = x - truncate(x / y) * y;

Assert(xy = n1 % n2);
Assert(xy = by_hand);