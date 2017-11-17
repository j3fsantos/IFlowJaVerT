
function top(o) {
    for(var p in o) {
	var s = o[p].replace("script", "s");
	assert(! s.contains("script"));
	o[p] = s;
    }
    return 0;
}

var o = { };

o[ ___p1_string ] = ___v1_string;
o[ "ok" ] = "safe";
o[ ___p2_string ] = ___v2_string;

top(o);
