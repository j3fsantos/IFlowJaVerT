
function f_three() { var o = { x: 0, y: 5, z: 10}; return o.z; }

function f_two() { var o = { x: 0, y: 5, z: 10}; return o.y; }

function f_one() { var o = { x: 0, y: 5, z: 10}; return o.x; }

function top(f, n) {
    var o = { one: f_one, two: f_two, three: f_three };
    var fun = o[f];
    if (fun() == n) {
	return 1;
    } else {
	return 0;
    }
}

top("one", 0);
top("two", 1);
top("three", 10);
top(prop_string, 10);
