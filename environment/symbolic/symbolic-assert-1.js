function top(n) {
    var total = 0;
    for(var i = 0; i < n; i++) {
		total += i;    
	}
    return total;
}

var n_number = jsil_make_symbolic_number (); 
jsil_assume ((n_number > 0) && (n_number < 2) && (typeof(n_number) == "number")); 

var t = top(n_number);
jsil_assert((t != 1) && (t != 0)); 
t


