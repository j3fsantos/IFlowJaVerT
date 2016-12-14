
function top(n) {
    var total = 0;
    for(var i = 0; i < n; i++) {
	total += i;
	jsil_assert(total < 15);
    }
    return total;
}

var n_number = jsil_make_symbolic_number (); 

top(n_number);
