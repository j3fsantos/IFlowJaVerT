var n_number = symb_number (); 

function top() {

    var y = symb_string ();

    return function inner(x) {
	var str = "";
	for(var z = 0; z != x; z++) {
	    str = y + str;
	}
	return str;
    }
}

(top())( n_number );

