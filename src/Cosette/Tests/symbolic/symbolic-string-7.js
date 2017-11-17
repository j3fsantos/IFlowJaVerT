
function f_three() { return this.z; }

function f_two() { return this.y; }

function f_one() { return this.x; }

function f_top(f, n) {
    if (this[f]() == n) {
	return 1;
    } else {
	return 0;
    }
}

var o = { top: f_top, one: f_one, two: f_two, three: f_three, x: 0, y: 5, z: 10 };

o.top("one", 0);
o.top("two", 1);
o.top("three", 10);
o.top(___prop_string, 10);
