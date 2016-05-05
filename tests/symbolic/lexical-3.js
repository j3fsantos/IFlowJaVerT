
function top() {

    var y = "ab";

    return function inner(x) {
	var str = "";
	for(var z = 0; z != x; z++) {
	    str = y + str;
	}
	return str;
    }
}

(top())(3);
