function one() {
    return 1;
}

function two() {
    return 2;
}

function three() {
    return 3;
}

function top(f) {
    if (f == "one") {
	return one();
    } else if (f == "two") {
	return two();
    } else {
	return three();
    }
}

top("two");
