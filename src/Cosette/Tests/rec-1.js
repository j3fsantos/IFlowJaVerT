/** 
  @return 8
*/

function top(x) {
    if (x < 3) {
	return 1;
    } else {
	return top(x-1) + top(x-2);
    }
}

var ret = top(6);
assert(ret = 8)

