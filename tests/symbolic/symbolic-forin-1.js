
function top(o) {
    var total = 0;
    for(var p in o) {
	total += o[p];
    }
    return total;
}

var o = { a: jsil_make_symbolic_number(),
	  b: jsil_make_symbolic_number(),
	  c: jsil_make_symbolic_number() };

var v = top(o);

jsil_assert(v = 100)
