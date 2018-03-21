var s1_string = symb_string(); 
var n1_number = symb_number(); 

Assume (n1_number < 9);

function extend(o) {
    for(var p in o) {
	this[p] = o[p];
    }
}

var Q = {
    extend: extend
};

var input = {
    s: s1_string,
    n: n1_number
};

Q.extend(input);

Assert(Q.n > 10);
