
function top(o) {
    var total = 0;
    for(var p in o) {
	total += o[p];
    }
    return total;
}

var o = { a: symb_number(),
	  b: symb_number(),
	  c: symb_number() };

var v = top(o);

Assert(v = 100)
