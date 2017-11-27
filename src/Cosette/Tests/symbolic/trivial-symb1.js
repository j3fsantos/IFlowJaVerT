var s = symb_string(s)
var n = symb_number(n)

var o = {}; 
o["foo"] = n; 

if (n > 0) { 
	var z = o[s]; 
	assert(not (z <= 0))
}