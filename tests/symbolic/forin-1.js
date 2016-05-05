
function top(o) {
    var total = 0;
    for(var p in o) {
	total += o[p];
    }
    return total;
}

var o = { a: 1, b: 2, c: 3 };

top(o);
