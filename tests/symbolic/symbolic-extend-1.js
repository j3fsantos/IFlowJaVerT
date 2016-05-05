
function extend(o) {
    for(p in o) {
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

assert(Q.n > 10);
