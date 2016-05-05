
function top() {

    var y = ___str_string;

    return function inner(x) {
	var str = "";
	for(var z = 0; z != x; z++) {
	    str = y + str;
	}
	return str;
    }
}

(top())( ___n_number );
