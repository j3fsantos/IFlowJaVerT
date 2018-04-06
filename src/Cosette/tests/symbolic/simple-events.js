var o = Object.create(null);

o.plusOne = function(x) { return x + 1 };
o.minusOne = function(x) { return x - 1 };

var s1 = symb_string(s1);
var s2 = symb_string(s2);
var n1 = symb_number(n1);
var n2 = symb_number(n2);

Assume(not (n1 = n2));

// figure out which functions to call
var total1 = o[s1](n1);
var total2 = o[s2](n2);

Assert(total1 = total2);