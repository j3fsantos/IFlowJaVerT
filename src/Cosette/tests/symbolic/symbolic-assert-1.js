function top(n) {
    var total = 0;
    for(var i = 0; i < n; i++) {
		total += i;    
	}
    return total;
}

var n1 = symb_number (n1); 
Assume ((n1 > 2) and (n1 < 6)); 

var t = top(n1);
Assert((not (t = 1)) and (not (t = 0))); 
t