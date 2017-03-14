/** 
  @return "ababab"
*/
var y = "ab";

function top(z) {

    function inner(x) {
	var str = "";
	for(var z = 0; z != x; z++) {
	    str = y + str;
	}
	return str;
    }

    return inner(z);
}

top(3);
