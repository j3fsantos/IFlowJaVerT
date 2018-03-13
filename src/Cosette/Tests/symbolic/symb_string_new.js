var o = {}; 
var y = symb_string(y);

Assume ((y = "foo") or (y = "bar")); 

o.foo = 3; 
o.bar = 4; 
var z = o[y]; 
 
Assert (z > 0) 