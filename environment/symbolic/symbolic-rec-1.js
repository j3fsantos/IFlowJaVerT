
function top(x) {
    if (x < 3) {
	return 1;
    } else {
	return top(x-1) + top(x-2);
    }
}

var x = jsil_make_symbolic_number();
top(x);

