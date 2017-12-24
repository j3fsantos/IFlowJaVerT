var v = 0;
var s = jsil_make_symbolic_string();
var s1 = jsil_make_symbolic_string();
var s2 = jsil_make_symbolic_string();

if (s != s1) {
    if (s != s2) {
	if (s1 != s2) {
	    v = 5;
	}
    }
}

jsil_Assert(v === 5)




