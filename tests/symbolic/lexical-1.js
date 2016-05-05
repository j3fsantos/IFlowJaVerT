
var y = "ab";

function top(x) {
    var str = "";
    for(var z = 0; z != x; z++) {
	str = y + str;
    }
    return str;
}

top(3);
