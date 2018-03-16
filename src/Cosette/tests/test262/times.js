// Comes from: ch11/11.5/11.5.1/S11.5.1_A4_T2.js

//CHECK#1
var x = symb_number (n1);
var y = symb_number (n2);
var xy = x * y; // JS-level multiplication
Assert(xy = n1 * n2); // Symbolic-level multiplication

// what to do with these ?

// //CHECK#5
// if (0 * 0 !== 0) {
//   $ERROR('#5.1: 0 * 0 === 0. Actual: ' + (0 * 0));
// } else {
//   if (1 / (0 * 0) !== Number.POSITIVE_INFINITY) {
//     $ERROR('#5.2: 0 * 0 === + 0. Actual: -0');
//   }
// }
// 
// //CHECK#6
// if (0 * -0 !== -0) {
//   $ERROR('#6.1: 0 * -0 === 0. Actual: ' + (0 * -0));
// } else {
//   if (1 / (0 * -0) !== Number.NEGATIVE_INFINITY) {
//     $ERROR('#6.2: 0 * -0 === - 0. Actual: +0');
//   }
// }
// 
// //CHECK#7
// if (-0 * 0 !== -0) {
//   $ERROR('#7.1: -0 * 0 === 0. Actual: ' + (-0 * 0));
// } else {
//   if (1 / (-0 * 0) !== Number.NEGATIVE_INFINITY) {
//     $ERROR('#7.2: -0 * 0 === - 0. Actual: +0');
//   }
// }
// 
// //CHECK#8
// if (-0 * -0 !== 0) {
//   $ERROR('#8.1: -0 * -0 === 0. Actual: ' + (-0 * -0));
// } else {
//   if (1 / (-0 * -0) !== Number.POSITIVE_INFINITY) {
//     $ERROR('#8.2: 0 * -0 === - 0. Actual: +0');
//   }
// }
//

// Division tests, abstracting ch11/11.5/11.5.2/S11.5.2_A4_T2.js
var x = symb_number (n1);
var y = symb_number (n2);
var xy = x / y; // JS-level multiplication
Assert(xy = n1 / n2); // Symbolic-level multiplication

