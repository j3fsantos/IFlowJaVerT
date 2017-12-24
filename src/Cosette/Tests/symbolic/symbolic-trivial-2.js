var n = jsil_make_symbolic_number (); 
var y = 3 + 7 + n;
var z = y + 7;
jsil_Assert(z < 0); 
