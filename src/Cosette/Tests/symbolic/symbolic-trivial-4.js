var n = symb_number (n); 
Assume ((0 < n) and (n < 2000));
var o = {}; 
o.field = n;  
var y = 3 + 7 + o.field;
var z = y + 7;
Assert(not(z < 0)); 
