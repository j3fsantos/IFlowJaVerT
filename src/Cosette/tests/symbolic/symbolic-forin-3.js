
function top(o) {
    var count = 0;
    for(var p in o) {
	count += 1;
    }
    return count;
}

var o = { a: 1, b: 2, c: 3 };

o[ p1_string ] = 4;
o[ p2_string ] = 5;

top(o);
