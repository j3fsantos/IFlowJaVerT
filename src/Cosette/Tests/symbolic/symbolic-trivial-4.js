var n = jsil_make_symbolic_number (); 
jsil_assume ((n > 0) && (n < 2000));
var o = {}; 
o.field = n;  
var y = 3 + 7 + o.field;
var z = y + 7;
jsil_Assert(z < 0); 
