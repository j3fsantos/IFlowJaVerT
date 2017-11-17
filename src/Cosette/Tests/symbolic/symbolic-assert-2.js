var ___p1_string = jsil_make_symbolic_string (s1); 
var ___v1_number = jsil_make_symbolic_number (n1); 

function top(o) {
	var n = 0; 
    for(var p in o) {
		n = n + o[p]
    }
    return n;
}

//jsil_assume (___v1_number == 0); 
var o = { a: 4, b: 5, c: 6 };

o[___p1_string] = ___v1_number;

var t = top(o);

jsil_assert ((t > 15) && (___p1_string !== "")); 
//jsil_assert (___p1_string == "a"); 
t