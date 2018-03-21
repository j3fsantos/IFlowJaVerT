
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
input[ s1_string ] = s2_string;
input[ s3_string ] = n1_number;

Q.extend(input);

function inc(x) { return x + 1; }

Assert(inc(Q[ s4_string ]) != "11" || inc(Q[ s5_string ]) != 11);
