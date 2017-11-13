/** 
  @return "aaaaaa"
*/

function top(x, y) {
    var str = "";
    for(var z = 0; z != x; z++) {
	str = y + str;
    }
    return str;
}

top(3, "aa");
