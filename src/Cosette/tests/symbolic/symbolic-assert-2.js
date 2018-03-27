var p1_string = symb_string (s1); 
var v1_number = symb_number (n1); 

function top(o) {
	var n = 0; 
    for(var p in o) {
		n = n + o[p]
    }
    return n;
}

//Assume (v1_number == 0); 
var o = { a: 4, b: 5, c: 6 };

o[p1_string] = v1_number;

var t = top(o);

Assert (not (t = "")); 
//Assert (p1_string == "a"); 
t