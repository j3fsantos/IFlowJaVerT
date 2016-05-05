
function top(o) {
    for(var p in o) {
	assert(p != o[p]);
    }
    return 0;
}

var o = { a: 1, b: 2, c: 3 };

o[ "a" + ___p1_string ] = ("" + ___v1_string + "b");

top(o);
