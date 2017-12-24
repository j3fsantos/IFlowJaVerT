
var Q = {
    extend: function extend(o) {
	for(p in o) {
	    if (! (p in this)) {
		this[p] = o[p];
	    }
	}
    }
};


var input = { };
input[ ___s1_string ] = ___s2_string;
input[ ___s3_string ] = ___n1_number;

Q.extend(input);

function inc(x) { return x + 1; }

Assert(inc(Q[ ___s4_string ]) != "11" || inc(Q[ ___s5_string ]) != 11);
