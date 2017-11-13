/** 
  @return 1
*/

function top(f, n) {
    var o = { one: 3, two: 5, three: 7 };
    if (o[f] == n) {
	return 1;
    } else {
	return 0;
    }
}

top("two", 5);
