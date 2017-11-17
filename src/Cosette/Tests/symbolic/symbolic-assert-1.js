function top(n) {
    var total = 0;
    for(var i = 0; i < n; i++) {
		total += i;    
	}
    return total;
}

var n_number = jsil_make_symbolic_number (n1); 
jsil_assume ((n_number > 2) && (n_number < 6)); 

var t = top(n_number);
jsil_assert((t != 1) && (t != 0)); 
t


