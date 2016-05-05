
function f_three() { return 10; }

function f_two() { return 5; }

function f_one() { return 1; }

function top(f, n) {
    var o = { one: f_one, two: f_two, three: f_three };
    var fun = o[f];
    if (fun() == n) {
	return n;
    } else {
	return 0;
    }
}

f_one();
f_two();
f_three();

top(___pp_string, ___num_number);
