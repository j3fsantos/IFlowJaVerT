
function f_three() { return 10; }

function f_two() { return 5; }

function f_one() { return 1; }

function top(f, n) {
    var o = { f_one: f_one, f_two: f_two, f_three: f_three };
    var fun = o["f_" + f];
    if (fun() == n) {
	return n;
    } else {
	return 0;
    }
}

f_one();
f_two();
f_three();

top(___prop_string, ___nm_number);
