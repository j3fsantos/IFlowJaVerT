var ___n_number = jsil_make_symbolic_number (); 

function top(n) {
    var total = 0;
    for(var i = 0; i < n; i++) {
	total += i;
    }
    return total;
}

top(___n_number);
