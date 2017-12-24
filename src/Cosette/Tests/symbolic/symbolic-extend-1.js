var ___s1_string = jsil_make_symbolic_string(); 
var ___n1_number = jsil_make_symbolic_number(); 

jsil_assume (___n1_number < 9);

function extend(o) {
    for(var p in o) {
	this[p] = o[p];
    }
}

var Q = {
    extend: extend
};

var input = {
    s: ___s1_string,
    n: ___n1_number
};

Q.extend(input);

jsil_Assert(Q.n > 10);
