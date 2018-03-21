
function top(o) {
    for(var p in o) {
	var s = o[p].replace("script", "s");
	Assert(! s.contains("script"));
	o[p] = s;
    }
    return 0;
}

var o = { };

o[ p1_string ] = v1_string;
o[ "ok" ] = "safe";
o[ p2_string ] = v2_string;

top(o);
