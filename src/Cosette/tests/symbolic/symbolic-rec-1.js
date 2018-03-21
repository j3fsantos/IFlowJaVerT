
function top(x) {
    if (x < 3) {
	return 1;
    } else {
	return top(x-1) + top(x-2);
    }
}

var x = symb_number();
var y = top(x);

Assert(y == 34)
