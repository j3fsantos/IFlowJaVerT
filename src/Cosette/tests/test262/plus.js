// Comes from: ch11/11.6/11.6.1/S11.6.1_A2.1_T1.js

//CHECK#1
var x = 1 + 1;
Assert(x = 2);

//CHECK#2
var n1 = symb_number(n1);
var x1 = n1 + 1;
Assert(x1 = n1 + 1);

//CHECK#3
var n2 = symb_number(n2);
var y1 = 1 + n2;
Assert(y1 = 1 + n2);

//CHECK#4
var n3 = symb_number(n3);
var n4 = symb_number(n4);
var xy = n3 + n4;
Assert(xy = n3 + n4);

//CHECK#5
var o1 = new Object();
var o2 = new Object();
var s = symb_string(s1);

var n5 = symb_number(n5);
var n6 = symb_number(n6);

o1[s] = n5;
o2[s] = n6;
var x56 = o1[s] + o2[s];

Assert(x56 = n5 + n6);