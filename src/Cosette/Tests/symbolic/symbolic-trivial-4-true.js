var n = symb_number (n1);
Assume ((n > 0) and (n < 2000));
var o = {};
o.field = n;
var y = 3 + 7 + o.field;
var z = y + 7;
Assert(z > 0);