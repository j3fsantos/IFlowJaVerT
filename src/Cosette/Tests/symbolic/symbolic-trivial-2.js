var n = symb_number (); 
Assume((not (n < 0))); 
var y = 3 + 7 + n;
var z = y + 7;
Assert(not (z < 0)); 
