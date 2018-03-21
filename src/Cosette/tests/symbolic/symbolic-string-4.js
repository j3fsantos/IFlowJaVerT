
function f_three(o) { return o.z; }

function f_two(o) { return o.y; }

function f_one(o) { return o.x; }

function top(f, n) {
    var o = { one: f_one, two: f_two, three: f_three };
    var data = { x: 0, y: 5, z: 10};

    var fun = o[f];
    if (fun(data) == n) {
	return 1;
    } else {
	return 0;
    }
}

top("one", 0);
top("two", 1);
top("three", 10);
top(prop_string, n_number);
