var n_number = jsil_make_symbolic_number (); 

function top() {

    var y = jsil_make_symbolic_string ();

    return function inner(x) {
	var str = "";
	for(var z = 0; z != x; z++) {
	    str = y + str;
	}
	return str;
    }
}

(top())( n_number );

